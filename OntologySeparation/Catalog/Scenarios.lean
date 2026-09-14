import OntologySeparation.Core.Protocol

/-! Four reference protocols plus the original ten research directions.
`obligations` distinguishes an executable toy from its unsolved research ambition. -/
namespace OntologySeparation.Catalog

/-- Closed set of bundled example families; mathematical Core interfaces remain generic. -/
inductive Family where
  | bell | lf | lfControl | echo | leak | phase | research
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure Scenario where
  id : String
  title : String
  family : Family
  protocol : ProtocolDescription
  obligations : String
  deriving Repr, Lean.ToJson, Lean.FromJson

def b01 : Scenario where
  id := "B01"
  title := "Bell CHSH"
  family := .bell
  protocol := {
    systems := ["alice", "bob"]
    preparation := "Prepare a bipartite singlet; independently choose two local bases."
    operations := [
      { action := "choose_local_bases", systems := ["alice", "bob"], requires := [] },
      { action := "measure", systems := ["alice", "bob"], requires := [] }
    ]
    settings := ["Alice 0/1", "Bob 0/1"]
    outcomes := ["a = +/-1", "b = +/-1"]
    observable := "S = E00 + E01 + E10 - E11"
  }
  obligations := "Close laboratory loopholes separately from the ideal theorem."

def b02 : Scenario where
  id := "B02"
  title := "Genuine Local Friendliness"
  family := .lf
  protocol := {
    systems := ["alice", "charlie", "bob", "debbie"]
    preparation := "Prepare singlet and two blank friend memories."
    operations := [
      { action := "record", systems := ["alice", "charlie"], requires := ["physical_memory"] },
      { action := "record", systems := ["bob", "debbie"], requires := ["physical_memory"] },
      { action := "ask_or_reverse", systems := ["alice", "charlie", "bob", "debbie"], requires := ["coherent_reversal"] },
      { action := "measure", systems := ["alice", "bob"], requires := [] }
    ]
    settings := ["ask friend", "alternative 1", "alternative 2"]
    outcomes := ["a = +/-1", "b = +/-1"]
    observable := "Bong et al. Eq. 13 score; LF bound 6"
  }
  obligations := "Ideal reversible friend model; no claim that a qubit is a cognitive observer."

def b03 : Scenario where
  id := "B03"
  title := "Bell violation compatible with LF"
  family := .lfControl
  protocol := {
    systems := ["alice", "bob", "charlie", "debbie"]
    preparation := "Fix friend records; permit a conditional PR inner box."
    operations := [
      { action := "read_friend_or_inner_box", systems := ["alice", "bob", "charlie", "debbie"], requires := [] }
    ]
    settings := ["ask friend", "alternative 1", "alternative 2"]
    outcomes := ["a = +/-1", "b = +/-1"]
    observable := "CHSH on non-friend settings"
  }
  obligations := "This is a postquantum LF-compatible witness, not a quantum implementation."

def b04 : Scenario where
  id := "B04"
  title := "Memory reversal calibration"
  family := .echo
  protocol := {
    systems := ["signal", "memory"]
    preparation := "Prepare signal |+> and memory |0>."
    operations := [
      { action := "record", systems := ["signal", "memory"], requires := ["physical_memory"] },
      { action := "reverse", systems := ["signal", "memory"], requires := ["coherent_reversal"] },
      { action := "measure_X", systems := ["signal"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "P(signal = +)"
  }
  obligations := "Two-qubit calibration only."

def p01 : Scenario where
  id := "P01"
  title := "Relative facts fail to compose"
  family := .research
  protocol := {
    systems := ["lab_a", "lab_b", "lab_c", "collector"]
    preparation := "Prepare three laboratories with overlapping accessible records."
    operations := [
      { action := "record_local_views", systems := ["lab_a", "lab_b", "lab_c"], requires := ["physical_memory"] },
      { action := "join_views", systems := ["lab_a", "lab_b", "lab_c"], requires := ["view_composition"] },
      { action := "compare_public_records", systems := ["collector"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Compatibility of pairwise views with one joint model"
  }
  obligations := "Define the cross-view composition rule and a feasible joint intervention; no separating theory pair is established."

def p02 : Scenario where
  id := "P02"
  title := "Conservation and public records versus reversal"
  family := .leak
  protocol := {
    systems := ["signal", "memory", "environment"]
    preparation := "Prepare signal |+> and blank memory; allow unobserved record leakage."
    operations := [
      { action := "record", systems := ["signal", "memory"], requires := ["physical_memory"] },
      { action := "leak_record", systems := ["memory", "environment"], requires := ["record_leakage"] },
      { action := "reverse_accessible", systems := ["signal", "memory"], requires := ["coherent_reversal"] },
      { action := "measure_X", systems := ["signal"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "P(signal = +) after inaccessible leakage"
  }
  obligations := "Exact leakage toy is included; conserved charge, reference-frame resources and the radical claim remain unformalized."

def p03 : Scenario where
  id := "P03"
  title := "Hidden causal cost of absolute facts"
  family := .research
  protocol := {
    systems := ["alice", "bob", "charlie", "debbie"]
    preparation := "Prepare an extended friend experiment with a bounded communication resource."
    operations := [
      { action := "record", systems := ["alice", "bob", "charlie", "debbie"], requires := ["physical_memory"] },
      { action := "bounded_causal_influence", systems := ["alice", "bob"], requires := ["causal_budget"] },
      { action := "measure", systems := ["alice", "bob"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Minimum causal influence needed to explain an LF score"
  }
  obligations := "Choose an influence metric and prove the tradeoff from the permitted causal model."

def p04 : Scenario where
  id := "P04"
  title := "Coherent experimenter choices"
  family := .phase
  protocol := {
    systems := ["control", "memory"]
    preparation := "Prepare a coherent control qubit and blank memory."
    operations := [
      { action := "record_control", systems := ["control", "memory"], requires := ["physical_memory"] },
      { action := "phase_flip", systems := ["control"], requires := ["coherent_control"] },
      { action := "reverse", systems := ["control", "memory"], requires := ["coherent_reversal"] },
      { action := "measure_X", systems := ["control"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "P(control = +) after phase-controlled memory echo"
  }
  obligations := "Exact coherent-control toy; a full choice-absoluteness theorem requires a separate protocol and assumptions."

def p05 : Scenario where
  id := "P05"
  title := "Observer identity and subsystem boundaries"
  family := .research
  protocol := {
    systems := ["laboratory", "collector"]
    preparation := "Prepare a composite system with two proposed subsystem factorizations."
    operations := [
      { action := "change_factorization", systems := ["laboratory"], requires := ["subsystem_relabeling"] },
      { action := "recover_accessible_record", systems := ["laboratory"], requires := ["restricted_access"] },
      { action := "compare_readout", systems := ["collector"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Recoverable information under each physical access map"
  }
  obligations := "Specify operationally different access maps; a passive relabeling alone cannot change predictions."

def p06 : Scenario where
  id := "P06"
  title := "Observations with indefinite causal order"
  family := .research
  protocol := {
    systems := ["target", "control", "lab_a", "lab_b", "collector"]
    preparation := "Prepare target and coherent order control with two friend laboratories."
    operations := [
      { action := "controlled_order", systems := ["target", "control", "lab_a", "lab_b"], requires := ["indefinite_order"] },
      { action := "record", systems := ["lab_a", "lab_b"], requires := ["physical_memory"] },
      { action := "measure_order_witness", systems := ["control", "collector"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Causal-order witness jointly with friend correlations"
  }
  obligations := "Requires a process-matrix or higher-order-map interpreter; a fixed-order circuit interpreter is insufficient."

def p07 : Scenario where
  id := "P07"
  title := "Gravitating records"
  family := .research
  protocol := {
    systems := ["mass_a", "mass_b", "gravity"]
    preparation := "Prepare spatial superpositions whose branches create distinct physical records."
    operations := [
      { action := "record_mass_branch", systems := ["mass_a", "mass_b"], requires := ["physical_memory"] },
      { action := "mediate_interaction", systems := ["mass_a", "mass_b", "gravity"], requires := ["gravitational_dynamics"] },
      { action := "reverse_local_record", systems := ["mass_a", "mass_b"], requires := ["coherent_reversal"] },
      { action := "measure_entanglement", systems := ["mass_a", "mass_b"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Entanglement witness and local visibility"
  }
  obligations := "Supply explicit mediator dynamics, coupling/time/noise parameters and competing classical model; no generic classical-gravity prediction."

def p08 : Scenario where
  id := "P08"
  title := "Computationally limited objectivity"
  family := .research
  protocol := {
    systems := ["memory", "environment", "collector"]
    preparation := "Encode a record in a many-body system; constrain the decoder."
    operations := [
      { action := "scramble_record", systems := ["memory", "environment"], requires := ["many_body_dynamics"] },
      { action := "bounded_decode", systems := ["memory"], requires := ["resource_bound"] },
      { action := "measure_recovery", systems := ["collector"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Best recovery probability at a specified query or circuit budget"
  }
  obligations := "Formalize the algorithm class and lower bound; this direction was set aside as a breakthrough claim."

def p09 : Scenario where
  id := "P09"
  title := "Observer versus reversible machine"
  family := .echo
  protocol := {
    systems := ["signal", "memory"]
    preparation := "Prepare a signal and a reversible physical memory device."
    operations := [
      { action := "record", systems := ["signal", "memory"], requires := ["physical_memory"] },
      { action := "reverse", systems := ["signal", "memory"], requires := ["coherent_reversal"] },
      { action := "measure_X", systems := ["signal"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "P(signal = +) after physical-memory reversal"
  }
  obligations := "Same exact memory toy as calibration; cognition, consciousness and functioning observers are not modeled."

def p10 : Scenario where
  id := "P10"
  title := "Rules of shared reality"
  family := .research
  protocol := {
    systems := ["agent_a", "agent_b", "agent_c", "collector"]
    preparation := "Prepare a network of agents receiving overlapping experimental records."
    operations := [
      { action := "collect_views", systems := ["agent_a", "agent_b", "agent_c"], requires := ["physical_memory"] },
      { action := "compose_views", systems := ["agent_a", "agent_b", "agent_c"], requires := ["view_composition"] },
      { action := "test_consistency", systems := ["collector"], requires := [] }
    ]
    settings := ["protocol as specified"]
    outcomes := ["public readout specified by observable"]
    observable := "Existence of a compatible public behavior under a composition rule"
  }
  obligations := "Specify operational composition axioms and prove a separation or equivalence; no automatic new physics claim."

def scenarios : List Scenario := [b01, b02, b03, b04, p01, p02, p03, p04, p05, p06, p07, p08, p09, p10]

end OntologySeparation.Catalog
