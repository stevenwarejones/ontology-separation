import OntologySeparation.PartialEnvironment

noncomputable section
open OntologySeparation

-- The hidden branch records have overlap at least 3/5.
-- These are probability allowances, not measured confidence intervals.
def study := PartialEnvironment.design (3/5) (1/20) (1/25)

def capacity := study.capacity
def coherentProbability := study.coherentProbability
def collapsedProbability := study.collapsedProbability
def margin := study.margin
def allTestsBound := study.bound

#export_claim capacity
#export_claim coherentProbability
#export_claim collapsedProbability
#export_claim margin
#export_claim allTestsBound
#export_theorem OntologySeparation.PartialEnvironment.uniform_threshold
#export_theorem OntologySeparation.PartialEnvironment.worst_case
#export_theorem OntologySeparation.PartialEnvironment.no_fragment_test
