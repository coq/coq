Module Type DagDefinitions.
End DagDefinitions.
Module DagExtraDefinitions (dag : DagDefinitions).

  Module Type EagerDagDefinitions.
  End EagerDagDefinitions.
End DagExtraDefinitions.
Include DagExtraDefinitions.
Declare Module eager : EagerDagDefinitions.
