import OntologySeparation.LocalFriendliness

namespace FriendStudy
open OntologySeparation.LocalFriendlinessRecipe

-- Four physical registers: Alice, Bob, Charlie's record, Debbie's record.
-- Setting 0 reads a record. Settings 1 and 2 undo that copy, then measure the system.
-- The reference source and relative bases reproduce the established LF witness.
def product : Recipe := { reference with source := .of 1 0 0 0 }

-- Charlie numerator, Debbie numerator, common denominator.
-- Noise acts on the records AFTER the friends copy and BEFORE Wigner chooses.
def comparison := compare "FriendStudy: read or reverse the friends"
  [Law.coherent, Law.recordDephasing 1 0 4,
   Law.recordDephasing 1 0 2, Law.recordDephasing 1 1 1]
  [reference, product]
end FriendStudy

#export_scenario FriendStudy.comparison
#export_theorem OntologySeparation.LocalFriendlinessRecipe.coherent_excludes_LF
#export_theorem OntologySeparation.LocalFriendlinessRecipe.coherent_excludes_profile
#export_theorem OntologySeparation.LocalFriendlinessRecipe.fully_dephased_realizes_profile
