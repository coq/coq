# Coq XML Protocol

This document is based on documentation originally written by CJ Bell
for his [vscoq](https://github.com/siegebell/vscoq/) project.

Here, the aim is to provide a "hands on" description of the XML
protocol that coqtop and IDEs use to communicate. The protocol first appeared 
with Coq 8.5, and is used by CoqIDE. It will also be used in upcoming 
versions of Proof General.

A somewhat out-of-date description of the async state machine is
[documented here](https://github.com/ejgallego/jscoq/blob/master/etc/notes/coq-notes.md).
OCaml types for the protocol can be found in the [`ide/protocol/interface.ml` file](/ide/protocol/interface.ml).

Changes to the XML protocol are documented as part of [`dev/doc/changes.md`](/dev/doc/changes.md).

* [Commands](#commands)
  - [About](#command-about)
  - [Add](#command-add)
  - [EditAt](#command-editAt)
  - [Init](#command-init)
  - [Goal](#command-goal)
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

### <a name="command-add">**Add(stateId: integer, command: string, verbose: boolean)**</a>
Adds a toplevel command (e.g. vernacular, definition, tactic) to the given state.
`verbose` controls whether out-of-band messages will be generated for the added command (e.g. "foo is assumed" in response to adding "Axiom foo: nat.").
```html
<call val="Add">
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
</call>
```

#### *Returns*
* The added command is given a fresh `stateId` and becomes the next "tip".
```html
<value val="good">
  <pair>
    <state_id val="${newStateId}"/>
    <pair>
      <union val="in_l"><unit/></union>
      <string>${message}</string>
    </pair>
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
  <value val="fail"
      loc_s="${startOffsetOfError}"
      loc_e="${endOffsetOfError}">
    <state_id val="${stateId}"/>
    <richpp>${errorMessage}</richpp>
  </value>
  ```
  - Another kind of error, for example, Qed with a pending goal.	
  ```html
  <value val="fail"><state_id val="${stateId}"/><richpp>${errorMessage}</richpp></value>
  ```

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

* New focus; focusedQedStateId is the closing Qed of the new focus; senteneces between the two should be cleared
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
* Failure: If `stateId` is in an error-state and cannot be jumped to, `errorFreeStateId` is the parent state of ``stateId` that shopuld be edited instead. 
```html
<value val="fail" loc_s="${startOffsetOfError}" loc_e="${endOffsetOfError}">
  <state_id val="${errorFreeStateId}"/>
  ${errorMessage}
</value>
```

-------------------------------

### <a name="command-init">**Init()**</a>
* No options.
```html
<call val="Init"><option val="none"/></call>
```
* With options. Looking at
  [ide_slave.ml](https://github.com/coq/coq/blob/c5d0aa889fa80404f6c291000938e443d6200e5b/ide/ide_slave.ml#L355),
  it seems that `options` is just the name of a script file, whose path
  is added via `Add LoadPath` to the initial state.
```html
<call val="Init">
  <option val="some">
    <string>${options}</string>
  </option>
</call>
```
Providing the script file enables Coq to use .aux files created during
compilation. Those file contain timing information that allow Coq to
choose smartly between asynchronous and synchronous processing of
proofs.

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


### <a name="command-status">**Status(force: bool)**</a>
Returns information about the current proofs. CoqIDE typically sends this
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
* Include blacklist: `${constraintType} = "include_blacklist"`; `${constraintValue}` *is ommitted*.

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
CoqIDE sends the following settings (defaults in parentheses):
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

* <a name="feedback-custom">Custom</a>. A feedback message that Coq plugins can use to return structured results, including results from Ltac profiling. Optionally, `startPos` and `stopPos` define a range of offsets in the document that the message refers to; otherwise, they will be 0. `customTag` is intended as a unique string that identifies what kind of payload is contained in `customXML`.
```xml
<feedback object="state" route="0">
  <state_id val="${stateId}"/>
  <feedback_content val="custom">
    <loc start="${startPos}" stop="${stopPos}"/>
    <string>${customTag}</string>
    ${customXML}
  </feedback_content>
</feedback>
```

