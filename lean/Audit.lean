import PowerLambert

/- These checks fail if any additional axiom enters a final proof. -/

/-- info: 'PowerLambert.powerLambert_full_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerLambert.powerLambert_full_theorem

/-- info: 'PowerLambert.lambert_positiveWordFrequencies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerLambert.lambert_positiveWordFrequencies

/-- info: 'PowerLambert.lambert_not_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerLambert.lambert_not_normal

/-- info: 'PowerLambert.limitingLaw_entropy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerLambert.limitingLaw_entropy_zero
