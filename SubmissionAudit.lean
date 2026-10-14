module
import all Solution
import all KKP.SpectralWitness
import all KKP.Compression
import all KKP.Witness
import all KKP.Bridge
import all KKP.Certificate
import all BN.Spectral.Variational
import Lean.Util.CollectAxioms

#print axioms KKP.connected_counterexample_family
#print axioms KKP.unbounded_connected_counterexamples
#print axioms KKP.positive_compression_le

open Lean Elab Command in
run_cmd do
  let deps ← liftCoreM (`KKP.unbounded_connected_counterexamples).transitivelyUsedConstants
  logInfo m!"variational_used={deps.contains `BN.variational_lemma}"
  logInfo m!"positive_compression_used={deps.contains `KKP.positive_compression_le}"
  logInfo m!"graph_freeness_used={deps.contains `KKP.bridgeGraph_free}"
