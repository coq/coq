# Coq XML Protocol

This document is based on documentation originally written by CJ Bell
for his [vscoq](https://github.com/coq-community/vscoq/) project.

Here, the aim is to provide a "hands on" description of the XML
protocol that coqtop and IDEs use to communicate. The protocol first appeared 
with Coq 8.5, and is used by RocqDE, [vscoq legacy](https://github.com/coq-community/vscoq-legacy/), and other user interfaces.

A somewhat out-of-date description of the async state machine is
[documented here](https://github.com/ejgallego/jscoq/blob/v8.16/etc/notes/coq-notes.md).
OCaml types for the protocol can be found in the [`ide/protocol/interface.ml` file](/ide/protocol/interface.ml).

Changes to the XML protocol are documented as part of [`dev/doc/changes.md`](/dev/doc/changes.md).

* [Commands](#commands)
  - [About](#command-about)
  - [Add](#command-add)
  - [EditAt](#command-editAt)
  - [Init](#command-init)
  - [Goal](#command-goal)
  - [Subgoals](#command-subgoals)
  - [Status](#command-status)
  - [Query](#command-query)
  - [Evars](#command-evars)
  - [Hints](#command-hints)
  - [Search](#command-search)
  - [GetOptions](#command-getoptions)
  - [SetOptions](#command-setoptions)
  - [MkCases](#command-mkcases)
  - [StopWorker](#command-stopworker)
  - [PrintAst](#command-printast)
  - [Annotate](#command-annotate)
  - [Db_cmd](#command-db_cmd)
  - [Db_upd_bpts](#command-db_upd_bpts)
  - [Db_continue](#command-db_continue)
  - [Db_stack](#command-db_stack)
  - [Db_vars](#command-db_vars)
* [Feedback messages](#feedback)
  - [Added Axiom](#feedback-addedaxiom)
  - [Processing](#feedback-processing)
  - [Processed](#feedback-processed)
  - [Incomplete](#feedback-incomplete)
  - [Complete](#feedback-complete)
  - [GlobRef](#feedback-globref)
  - [Error](#feedback-error)
  - [InProgress](#feedback-inprogress)
  - [WorkerStatus](#feedback-workerstatus)
  - [File Dependencies](#feedback-filedependencies)
  - [File Loaded](#feedback-fileloaded)
  - [Message](#feedback-message)
  - [Custom](#feedback-custom)
* [Ltac-debug messages](ltac_debug)
* [Highlighting Text](#highlighting)

Sentences: each command sent to Coqtop is a "sentence"; they are typically terminated by ".\s" (followed by whitespace or EOF).
Examples: "Lemma a: True.", "(* asdf *) Qed.", "auto; reflexivity."
In practice, the command sentences sent to Coqtop are terminated at the "." and start with any previous whitespace.
Each sentence is assigned a unique stateId after being sent to Coq (via Add).
States:
  * Processing: has been received by Coq and has no obvious syntax error (that would prevent future parsing)
  * Processed:
  * InProgress:
  * Incomplete: the validity of the sentence cannot be checked due to a prior error
  * Complete:
  * Error: the sentence has an error

State ID 0 is reserved as a 'dummy' state.

--------------------------

## <a name="commands">Commands</a>

### <a name="command-about">**About(unit)**</a>
Returns information about the protocol and build dates for Coqtop.
```
<call val="About">
  <unit/>
</call>
```
#### *Returns*
```html
 <value val="good">
   <coq_info><string>8.6</string>
     <string>20150913</string>
     <string>December 2016</string>
     <string>Dec 23 2016 16:16:30</string>
   </coq_info>
</value>
```
The string fields are the Coq version, the protocol version, the release date, and the compile time of Coqtop.
The protocol version is a date in YYYYMMDD format, where "20150913" corresponds to Coq 8.6. An IDE that wishes 
to support multiple Coq versions can use the protocol version information to know how to handle output from Coqtop.

### <a name="command-add">**Add(command: string, editId: integer, stateId: integer, verbose: boolean, bp: integer, line_nb: integer, bol_pos: integer)**</a>
Adds a toplevel command (e.g. vernacular, definition, tactic) to the given state.
`verbose` controls whether out-of-band messages will be generated for the added command
(e.g. "foo is assumed" in response to adding "Axiom foo: nat.").  `bp`, `line_nb` and
`bol_pos` are the `Loc.t` values relative to the IDE buffer.

```html
<call val="Add">
  <pair>
    <pair>
      <pair>
        <pair>
          <string>${command}</string>
          <int>${editId}</int>
        </pair>
        <pair>
          <state_id val="${stateId}"/>
          <bool val="${verbose}"/>
        </pair>
      </pair>
      <int>${bp}</int>
    </pair>
    <pair>
      <int>${line_nb}</int>
      <int>${bol_pos}</int>
    </pair>
  </pair>
</call>
```

#### *Returns*
* The added command is given a fresh `stateId` and becomes the next "tip".
```html
<value val="good">
  <pair>
    <state_id val="${newStateId}"/>
    <union val="in_l">
      <unit/>
    </union>
  </pair>
</value>
```
* When closing a focused proof (in the middle of a bunch of interpreted commands),
the `Qed` will be assigned a prior `stateId` and `nextStateId` will be the id of an already-interpreted
state that should become the next tip. 
```html
<value val="good">
  <pair>
    <state_id val="${stateId}"/>
    <pair>
      <union val="in_r"><state_id val="${nextStateId}"/></union>
      <string>${message}</string>
    </pair>
  </pair>
</value>
```
* Failure:
  - Syntax error. Error offsets are byte offsets (not character offsets) with respect to the start of the sentence, starting at 0.
  ```html
  <value val="fail">
    <state_id val="${stateId}"/>
    <option val="none|some">${loc}</option>
    <richpp>${errorMessage}</richpp>
  </value>
  ```
  - Another kind of error, for example, Qed with a pending goal.	
  ```html
  <value val="fail"><state_id val="${stateId}"/><option val="some">${loc}</option><richpp>${errorMessage}</richpp></value>
  ```

  Note that IDEs may need to convert byte offsets passed in the four position fields of the
  location to character offsets to correctly handle multi-byte characters. Also, due to
  asynchronous evaluation, line number fields of locations may need to be adjusted
  if the sentence has moved since it was sent to Coqtop.

-------------------------------

### <a name="command-editAt">**EditAt(stateId: integer)**</a>
Moves current tip to `${stateId}`, such that commands may be added to the new state ID.
```html
<call val="Edit_at"><state_id val="${stateId}"/></call>
```
#### *Returns*
* Simple backtrack; focused stateId becomes the parent state
```html
<value val="good">
  <union val="in_l"><unit/></union>
</value>
```

* New focus; focusedQedStateId is the closing Qed of the new focus; sentences between the two should be cleared
```html
<value val="good">
  <union val="in_r">
    <pair>
      <state_id val="${focusedStateId}"/>
      <pair>
        <state_id val="${focusedQedStateId}"/>
        <state_id val="${oldFocusedStateId}"/>
      </pair>
    </pair>
  </union>
</value>
```
* Failure: If `stateId` is in an error-state and cannot be jumped to, `errorFreeStateId` is the parent state of `stateId` that should be edited instead.
```html
<value val="fail">
  <state_id val="${errorFreeStateId}"/>
  <option val="none|some">${loc}</option>
  ${errorMessage}
</value>
```

-------------------------------

### <a name="command-init">**Init()**</a>
* No options.
```html
<call val="Init"><option val="none"/></call>
```
* With options:
```html
<call val="Init">
  <option val="some">
    <string>${v_file}.v</string>
  </option>
</call>
```
Providing the script file `$v_file.v` enables Coq to use the `.$v_file.aux`
file created during compilation. Those file contain timing information
that allow Coq to choose smartly between asynchronous and synchronous
processing of proofs.

#### *Returns*
* The initial stateId (not associated with a sentence)
```html
<value val="good">
  <state_id val="${initialStateId}"/>
</value>
```

-------------------------------


### <a name="command-goal">**Goal()**</a>
```html
<call val="Goal"><unit/></call>
```
#### *Returns*
* If there is a goal. `shelvedGoals` and `abandonedGoals` have the same structure as the first set of (current/foreground) goals. `backgroundGoals` contains a list of pairs of lists of goals (list ((list Goal)*(list Goal))); it represents a "focus stack" ([see code for reference](https://github.com/coq/coq/blob/trunk/engine/proofview.ml#L113)). Each time a proof is focused, it will add a new pair of lists-of-goals. The first pair is the most nested set of background goals, the last pair is the top level set of background goals. The first list in the pair is in reverse order. Each time you focus the goal (e.g. using `Focus` or a bullet), a new pair will be prefixed to the list.
```html
<value val="good">
  <option val="some">
  <goals>
    <!-- current goals -->
    <list>
      <goal>
        <string>3</string>
        <list>
          <richpp>${hyp1}</richpp>
          ...
          <richpp>${hypN}</richpp>
        </list>
        <richpp>${goal}</richpp>
      </goal>
      ...
      ${goalN}
    </list>
    <!-- `backgroundGoals` -->
    <list>
      <pair>
        <list><goal />...</list>
        <list><goal />...</list>
      </pair>
      ...
    </list>
    ${shelvedGoals}
    ${abandonedGoals}
  </goals>
  </option>
</value>
```

For example, this script:
```coq
Goal P -> (1=1/\2=2) /\ (3=3 /\ (4=4 /\ 5=5) /\ 6=6) /\ 7=7.
intros.
split; split. (* current visible goals are [1=1, 2=2, 3=3/\(4=4/\5=5)/\6=6, 7=7] *)
Focus 3. (* focus on 3=3/\(4=4/\5=5)/\6=6; bg-before: [1=1, 2=2], bg-after: [7=7] *)
split; [ | split ]. (* current visible goals are [3=3, 4=4/\5=5, 6=6] *)
Focus 2. (* focus on 4=4/\5=5; bg-before: [3=3], bg-after: [6=6] *)
* (* focus again on 4=4/\5=5; bg-before: [], bg-after: [] *)
split. (* current visible goals are [4=4,5=5] *)
```
should generate the following goals structure:
```
goals: [ P|-4=4, P|-5=5 ]
background:
[
  ( [], [] ), (* bullet with one goal has no before or after background goals *)
  ( [ P|-3=3 ], [ P|-6=6 ] ), (* Focus 2 *)
  ( [ P|-2=2, P|-1=1 ], [ P|-7=7 ] ) (* Focus 3; notice that 1=1 and 2=2 are reversed *)
]
```
Pseudocode for listing all of the goals in order: `rev (flat_map fst background) ++ goals ++ flat_map snd background`.

* No goal:
```html
<value val="good"><option val="none"/></value>
```

-------------------------------

### <a name="command-subgoals">**Subgoals(flags: goal_flags)**</a>
Similar to [Goal](#command-goal), but with `flags` to control whether to include
information about `fg`, `bg`, `shelved`, or `given_up` goals. The flags also
include `mode`, which is either "full" (return hypotheses and conclusion for
each goal) or "short" (return only the conclusion). The "short" mode is useful
for speeding up goal display when there are many shelved or admitted goals with
large proof contexts, but the IDE only needs to know their conclusions or how
many there are.
```html
<call val="Subgoals">
  <goal_flags>
    <string>${mode}</string>
    <bool val="${fg}"/>
    <bool val="${bg}"/>
    <bool val="${shelved}"/>
    <bool val="${given_up}"/>
  </goal_flags>
</call>
```

#### Returns
* The same as [Goal](#command-goal).

-------------------------------

### <a name="command-status">**Status(force: bool)**</a>
Returns information about the current proofs. RocqIDE typically sends this
message with `force = false` after each sentence, and with `force = true` if
the user wants to force the checking of all proofs (wheels button). In terms of
the STM API, `force` triggers a `Join`.
```html
<call val="Status"><bool val="${force}"/></call>
```
#### *Returns*
*  
```html
<status>
  <string>${path}</string>
  <string>${proofName}</string>
  <string>${allProofs}</string>
  <string>${proofNumber}</string>
</status>
```

-------------------------------

### <a name="command-query">**Query(route_id: integer, query: string, stateId: integer)**</a>

`routeId` can be used to distinguish the result of a particular query,
`stateId` should be set to the state the query should be run.

```html
<call val="Query">
  <pair>
    <route_id val="${routeId}"/>
  <pair>
    <string>${query}</string>
    <state_id val="${stateId}"/>
  </pair>
  </pair>
</call>
```
#### *Returns*
*
```html
<value val="good">
  <string>${message}</string>
</value>
```

Before 8.8, `Query` only executed the first command present in the
`query` string; starting with 8.8, the caller may include several
statements. This is useful for instance for temporarily setting an
option and then executing a command.

-------------------------------



### <a name="command-evars">**Evars()**</a>
```html
<call val="Evars"><unit/></call>
```
#### *Returns*
*
```html
<value val="good">
  <option val="some">
    <list>
      <evar>${evar1}</evar>
      ...
      <evar>${evarN}</evar>
    </list>
  </option>
</value>
```

-------------------------------


### <a name="command-hints">**Hints()**</a>
```html
<call val="Hints"><unit/></call>
```
#### *Returns*
*
```html
<value val="good">
  <option val="some">
    <pair>
      <list/>
      <list>
        <pair>
          <string>${hint1}</string>
          <string>${hint2}</string>
        </pair>
        ...
        <pair>
          <string>${hintN-1}</string>
          <string>${hintN}</string>
        </pair>
      </list>
    </pair>
  </option>
</value>
```

-------------------------------


### <a name="command-search">**Search([(constraintTypeN: string, constraintValueN: string, positiveConstraintN: boolean)])**</a>
Searches for objects that satisfy a list of constraints. If `${positiveConstraint}` is `false`, then the constraint is inverted. 
```html
<call val="Search">
  <list>
    <pair>
      <search_cst val="${constraintType1}">
        ${constraintValue1}
      </search_cst>
      <bool val="${positiveConstraint1}"/>
    </pair>
    ...
    <!-- Example: -->
    <pair>
      <search_cst val="name_pattern">
        <string>bool_rect</string>
      </search_cst>
      <bool val="true"/>
    </pair>
  </list>
</call>
```
#### *Returns*
*
```html
<value val="good">
  <list>
      <coq_object>
          <list>
              <string>${metaInfo}</string>
              ...
          </list>
          <list>
              <string>${name}</string>
          </list>
          <string>${definition}</string>
      </coq_object>
      ...
  </list>
</value>
```
##### Types of constraints:
* Name pattern: `${constraintType} = "name_pattern"`; `${constraintValue}` is a regular expression string.
* Type pattern: `${constraintType} = "type_pattern"`; `${constraintValue}` is a pattern (???: an open gallina term) string.
* SubType pattern: `${constraintType} = "subtype_pattern"`; `${constraintValue}` is a pattern (???: an open gallina term) string.
* In module: `${constraintType} = "in_module"`; `${constraintValue}` is a list of strings specifying the module/directory structure.
* Include blacklist: `${constraintType} = "include_blacklist"`; `${constraintValue}` *is omitted*.

-------------------------------


### <a name="command-getoptions">**GetOptions()**</a>
```html
<call val="GetOptions"><unit/></call>
```
#### *Returns*
*
```html
<value val="good">
  <list>
    <pair>
      <list><string>${string1}</string>...</list>
      <option_state>
        <bool>${sync}</bool>
        <bool>${deprecated}</bool>
        <string>${name}</string>
        ${option_value}
      </option_state>
    </pair>
    ...
  </list>
</value>
```

-------------------------------


### <a name="command-setoptions">**SetOptions(options)**</a>
Sends a list of option settings, where each setting roughly looks like:
`([optionNamePart1, ..., optionNamePartN], value)`.
```html
<call val="SetOptions">
  <list>
    <pair>
      <list>
        <string>optionNamePart1</string>
        ...
        <string>optionNamePartN</string>
      </list>
      <option_value val="${typeOfOption}">
        <option val="some">
          ${value}
        </option>
      </option_value>
    </pair>
    ...
    <!-- Example: -->
    <pair>
      <list>
        <string>Printing</string>
        <string>Width</string>
      </list>
      <option_value val="intvalue">
        <option val="some"><int>60</int></option>
      </option_value>
    </pair>
  </list>
</call>
```
RocqIDE sends the following settings (defaults in parentheses):
```
Printing Width : (<option_value val="intvalue"><int>60</int></option_value>),
Printing Coercions : (<option_value val="boolvalue"><bool val="false"/></option_value>),
Printing Matching : (...true...)
Printing Notations : (...true...)
Printing Existential Instances : (...false...)
Printing Implicit : (...false...)
Printing All : (...false...)
Printing Universes : (...false...)
```
#### *Returns*
*
```html
<value val="good"><unit/></value>
```

-------------------------------


### <a name="command-mkcases">**MkCases(...)**</a>
```html
<call val="MkCases"><string>...</string></call>
```
#### *Returns*
*
```html
<value val="good">
  <list>
    <list><string>${string1}</string>...</list>
    ...
  </list>
</value>
```

-------------------------------


### <a name="command-stopworker">**StopWorker(worker: string)**</a>
```html
<call val="StopWorker"><string>${worker}</string></call>
```
#### *Returns*
*
```html
<value val="good"><unit/></value>
```

-------------------------------


### <a name="command-printast">**PrintAst(stateId: integer)**</a>
```html
<call val="PrintAst"><state_id val="${stateId}"/></call>
```
#### *Returns*
*
```html
<value val="good">
  <gallina begin="${gallina_begin}" end="${gallina_end}">
    <theorem begin="${theorem_begin}" end="${theorem_end}" type="Theorem" name="${theorem_name}">
      <apply begin="${apply_begin}" end="${apply_end}">
        <operator begin="${operator_begin}" end="${operator_end}" name="${operator_name}"/>
        <typed begin="${typed_begin}" end="${typed_end}">
          <constant begin="${constant_begin}" end="${constant_end}" name="${constant_name}"/>
          ...
          <token begin="${token_begin}" end="token_end">${token}</token>
          ...
        </typed>
        ...
      </apply>
    </theorem>
    ...
  </gallina>
</value>
```

-------------------------------



### <a name="command-annotate">**Annotate(annotation: string)**</a>
```html
<call val="Annotate"><string>${annotation}</string></call>
```
#### *Returns*
*

take `<call val="Annotate"><string>Theorem plus_0_r : forall n : nat, n + 0 = n.</string></call>` as an example.

```html
<value val="good">
  <pp startpos="0" endpos="45">
    <vernac_expr startpos="0" endpos="44">
      <keyword startpos="0" endpos="7">Theorem</keyword>
      &nbsp;plus_0_r&nbsp;:&nbsp;
      <constr_expr startpos="19" endpos="44">
        <keyword startpos="19" endpos="25">forall</keyword>
        &nbsp;n&nbsp;:&nbsp;
        <constr_expr startpos="30" endpos="33">nat</constr_expr>
        ,&nbsp;
        <unparsing startpos="35" endpos="44">
          <unparsing startpos="35" endpos="40">
            <unparsing startpos="35" endpos="40">
              <unparsing startpos="35" endpos="36">
                <constr_expr startpos="35" endpos="36">n</constr_expr>
              </unparsing>
              <unparsing startpos="36" endpos="38">&nbsp;+</unparsing>
              <unparsing startpos="38" endpos="39">&nbsp;</unparsing>
              <unparsing startpos="39" endpos="40">
                <constr_expr startpos="39" endpos="40">0</constr_expr>
              </unparsing>
            </unparsing>
          </unparsing>
          <unparsing startpos="40" endpos="42">&nbsp;=</unparsing>
          <unparsing startpos="42" endpos="43">&nbsp;</unparsing>
          <unparsing startpos="43" endpos="44">
            <constr_expr startpos="43" endpos="44">n</constr_expr>
          </unparsing>
        </unparsing>
      </constr_expr>
    </vernac_expr>
    .
  </pp>
</value>
```

-------------------------------



### <a name="command-db_cmd">**Db_cmd(user_input: string)**</a>
```html
<call val="Db_cmd"><string>${user_input}</string></call>
```
#### *Returns*
*

`<call val="Db_cmd"><string>h</string></call>` directs Coq to process the debugger command "h".
It returns unit.  This call is processed only when the debugger is stopped and has just
sent a `prompt` message.



-------------------------------



### <a name="command-db_upd_bpts">**Db_upd_bpts(...)**</a>
The call passes a list of breakpoints to set or clear.  The string is the
absolute pathname of the .v file (or "ToplevelInput"), the int is the byte offset
within the file and the boolean is true to set a breakpoint and false to clear it.
Breakpoints can be updated when Coq is not busy or when Coq is stopped in the
debugger.  If this message is sent in other states, it will be received and
processed when Coq is no longer busy or execution stops in the debugger.

```html
<call val="Db_upd_bpts">
  <list>
    <pair>
      <pair>
        <string>/home/proj/coq/ide/rocqide/debug.v</string>
        <int>22</int>
      </pair>
      <bool val="true"/>
    </pair>
  </list>
</call>
```
#### *Returns*
* Unit.



-------------------------------




### <a name="command-db_continue">**Db_continue(option: integer)**</a>

Tells Coq to continue processing the proof when it is stopped in the debugger.
The integer indicates when the debugger should stop again:

```
0: StepIn - step one tactic.  If it is an Ltac tactic, stop at the first tactic within it
1: StepOver - step over one tactic.  if it is an Ltac tactic, don't stop within it
2: StepOut - stop on the first tactic after exiting the current Ltac tactic
3: Continue - continue running until the next breakpoint or the debugger exits
4: Interrupt - generate a User interrupt (for use when stopped in the debugger; otherwise
     interrupt is sent as a signal)
```

If the debugger encounters a breakpoint during a StepOver or a StepOut, it will
stop at the breakpoint.

```html
<call val="Db_continue">
  <int>1</int>
</call>
```

#### *Returns*
* Unit.



### <a name="command-db_stack">**Db_stack()**</a>

Returns the Ltac call stack.  Each entry has a description of what was called
(e.g. the tactic name) plus the absolute pathname of the file and the offset of
the call therein.  The top of stack is the first entry in the list.  Offsets
are in bytes, not counts of unicode characters.

```html
<call val="Db_stack">
  </unit>
</call>
```

#### *Returns*
```html
<value val="good">
  <list>
    <pair>
      <string>vars2.z</string>
      <option val="some">
        <pair>
          <string>ToplevelInput</string>
          <list>
            <int>51</int>
            <int>58</int>
          </list>
        </pair>
      </option>
    </pair>
      :
  </list>
</value>
```


### <a name="command-db_vars">**Db_vars(frame: integer)**</a>

Returns a list of the names and values of the local variables defined in the
specified frame of the Ltac call stack.  (0 = top of stack, 1, 2, ...).

```html
<call val="Db_vars">
  <int>0</int>
</call>
```

#### *Returns*
```html
<value val="good">
  <list>
    <pair>
      <string>w</string>
      <ppdoc val="string">
        <string>0</string>
      </ppdoc>
    </pair>
      :
  </list>
</value>
```


-------------------------------

## <a name="feedback">Feedback messages</a>

Feedback messages are issued out-of-band,
  giving updates on the current state of sentences/stateIds,
  worker-thread status, etc.

In the descriptions of feedback syntax below, wherever a `state_id`
tag may occur, there may instead be an `edit_id` tag.

* <a name="feedback-addedaxiom">Added Axiom</a>: in response to `Axiom`, `admit`, `Admitted`, etc.
```html
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="addedaxiom" />
</feedback>
```
* <a name="feedback-processing">Processing</a>
```html
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="processingin">
    <string>${workerName}</string>
  </feedback_content>
</feedback>
```
* <a name="feedback-processed">Processed</a>
```html
<feedback object="state" route="0">
  <feedback object="state" route="0">
    <state_id val="${stateId}"/>
  <feedback_content val="processed"/>
</feedback>
```
* <a name="feedback-incomplete">Incomplete</a>
```html
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="incomplete" />
</feedback>
```
* <a name="feedback-complete">Complete</a>
* <a name="feedback-globref">GlobRef</a>
* <a name="feedback-error">Error</a>. Issued, for example, when a processed tactic has failed or is unknown.
The error offsets may both be 0 if there is no particular syntax involved.
* <a name="feedback-inprogress">InProgress</a>
```html
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="inprogress">
    <int>1</int>
  </feedback_content>
</feedback>
```
* <a name="feedback-workerstatus">WorkerStatus</a>
Ex: `workername = "proofworker:0"`
Ex: `status = "Idle"` or `status = "proof: myLemmaName"` or `status = "Dead"`
```html
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="workerstatus">
    <pair>
      <string>${workerName}</string>
      <string>${status}</string>
    </pair>
  </feedback_content>
</feedback>
```
* <a name="feedback-filedependencies">File Dependencies</a>. Typically in response to a `Require`. Dependencies are *.vo files.
  - State `stateId` directly depends on `dependency`:
  ```html
  <feedback object="state" route="0">
    <state_id val="${stateId}"/>
    <feedback_content val="filedependency">
      <option val="none"/>
      <string>${dependency}</string>
    </feedback_content>
  </feedback>
  ```
  - State `stateId` depends on `dependency` via dependency `sourceDependency`
  ```xml
  <feedback object="state" route="0">
    <state_id val="${stateId}"/>
    <feedback_content val="filedependency">
      <option val="some"><string>${sourceDependency}</string></option>
      <string>${dependency}</string>
    </feedback_content>
  </feedback>
  ```
* <a name="feedback-fileloaded">File Loaded</a>. For state `stateId`, module `module` is being loaded from `voFileName`
```xml
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="fileloaded">
    <string>${module}</string>
    <string>${voFileName`}</string>
  </feedback_content>
</feedback>
```

* <a name="feedback-message">Message</a>. `level` is one of `{info,warning,notice,error,debug}`. For example, in response to an <a href="#command-add">add</a> `"Axiom foo: nat."` with `verbose=true`, message `foo is assumed` will be emitted in response.
```xml
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="message">
    <message>
      <message_level val="${level}"/>
      <string>${message}</string>
    </message>
  </feedback_content>
</feedback>
```
* <a name="location">Location</a>, a Coq location (`Loc.t`)
```xml
   <loc start="${start_offset}" stop="${stop_offset}
        line_nb="${start_line}" bol_pos="${begin_of_start_line_offset}"
        line_nb_last="${end_line}" bol_pos_last="${begin_of_end_line_offset}"
```

* <a name="feedback-custom">Custom</a>. A feedback message that Coq plugins can use to return structured results, including results from Ltac profiling. `customTag` is intended as a unique string that identifies what kind of payload is contained in `customXML`. An optional location may be attached if present in the message.
```xml
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="custom">
    <option val="none|some">${loc}</option>
    <string>${customTag}</string>
    ${customXML}
  </feedback_content>
</feedback>
```

-------------------------------

## <a name="ltac-debug">Ltac-debug messages</a>

Ltac-debug messages are issued out-of-band, similar to Feedback messages.
The response contains an identifying tag and a `<ppdoc>`.
Currently these tags are used:

* **output** - ordinary output for display in the Messages panel
* **goal** - the current goal for the debugger, for display in the Messages panel
  or elsewhere
* **prompt** - output for display in the Messages panel prompting the user to
  enter a debug command, allowing RocqIDE to display it without
  appending a newline.  It also signals that coqidetop is waiting to receive
  a debugger-specific message such as [Db_cmd](#command-db_cmd).

```xml
<ltac_debug>
prompt
  <ppdoc val="tag">
        :
  </ppdoc>
</ltac_debug>
```

-------------------------------

## <a name="highlighting">Highlighting Text</a>

[Proof diffs](https://coq.inria.fr/distrib/current/refman/proof-engine/proof-handling.html#showing-differences-between-proof-steps)
highlight differences between the current and previous proof states in the displayed output.
These are represented by tags embedded in output fields of the XML document.

There are 4 tags that indicate how the enclosed text should be highlighted:
- diff.added - added text
- diff.removed - removed text
- diff.added.bg - unchanged text in a line that has additions ("bg" for "background")
- diff.removed.bg - unchanged text in a line that has removals

RocqIDE, Proof General and coqtop currently use 2 shades of green and 2 shades of red
as the background color for highlights.  Coqtop and RocqIDE also apply underlining and/or
strikeout highlighting for the sake of the color blind.

For example, `<diff.added>ABC</diff.added>` indicates that "ABC" should be highlighted
as added text.  Tags can be nested, such as:
`<diff.added.bg>A <diff.added> + 1</diff.added> + B</diff.added.bg>`.  IDE code
displaying highlighted strings should maintain a stack for nested tags and the associated
highlight.  Currently the diff code only nests at most 2 tags deep.
If an IDE uses other highlights such as text foreground color or italic text, it may
need to merge the background color with those other highlights to give the desired
(IDE dependent) behavior.

The current implementations avoid highlighting white space at the beginning or the
end of a line.  This gives a better appearance.

There may be additional text that is marked with other tags in the output text.  IDEs probably
should ignore and not display tags they don't recognize.

Some internal details about generating tags within Coq (e.g. if you want to add
additional tags):

Tagged output strings are generated from Pp.t's.  Use Pp.tag to highlight a Pp.t using
one of the tags listed above.  A span of tokens can be marked by using "start.<tag>" on
the first token and "end.<tag>" on the last token.  (Span markers are needed because a span of
tokens in the output may not match nesting of layout boxes in the Pp.t.)
The conversion from the Pp.t to the XML-tagged string replaces the "start.\*" and "end.\*"
tags with the basic tags.
