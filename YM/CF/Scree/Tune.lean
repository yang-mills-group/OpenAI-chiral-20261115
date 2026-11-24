import YM.CF.Scree.Locus
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m C B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
def beamL (n:Side) : Phys n →L[ℝ]ℂ:= (innerSL ℂ (mateK n)).restrictScalars ℝ
variable {R:GramM (mid m B)}{P:Grasp Y B e}{A:Loom (mid m B)} {R':GramM (mid C B)}{A':Loom (mid C B)}{G:Ratio (mid m B) (mid C B)}{T:RG.StepData (More (mid m B)) (More (mid C B))}{q:Chi}{d:ℝ}{Q:Op Slot}(E:RelayZ R P A R' A' G T q d Q)
include E
lemma relay_v (X:Orbit (mid m B))(W:Orbit (mid C B)): beamL (mid m B) (integrated P A R' A' G T q d Q X W)= T.density R'.beta W.1 X.1 • beamL (mid C B) (denZ R' P A' W):=by
 let L' :=ratio G; letI :Nonempty (Forest L'):= Tree.select L' (show Odd G.count.val from E.shape.symm ▸ ho)
 let v:=denZ R' P A' W
 have hp:Fintype.card (Forest L')≠0:= Fintype.card_ne_zero
 have ht(F: Forest L'):beamL (mid m B) (carrier P A R' A' G T q d Q F X W)= T.density R'.beta W.1 X.1 • beamL _ v:=by
    rw [carrier,map_smul]; apply congrArg (fun z:ℂ=> T.density _ W.1 X.1 • z); rw [show beamL _ (scaleZ _ _)= _ from E.wheel _]; change inner ℂ (mateK _) _= beamZ _ v; have hQ:= Spire.shuttle G E.shape E.size _ (E.eligible F X W) E.hot R'.J.M; rw [show inner ℂ _ _= _ from hQ.2 (cartsL (switchG G).symm v)] -- tune
    exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
 unfold integrated; rw [map_smul,map_sum]; rw [sum_congr rfl (fun i _=>ht i),sum_const,card_univ]
 simp only [nsmul_eq_mul,Complex.real_smul,Complex.ofReal_natCast,Complex.ofReal_inv]; rw [←mul_assoc, inv_mul_cancel₀,one_mul]; exact_mod_cast hp
lemma balanceX : partitionZ R P A=partitionZ R' P A':=by
 let U:=Orbit (mid m B); let V:=Orbit (mid C B); let K:=beamL (mid m B); let Λ:=beamL (mid C B); let F(X:U×V):= integrated P A R' A' G T q d Q X.1 X.2
 have ht: Integrable F ((city _).prod (city _)):= E.fed; have hp: Integrable (fun x=>K (F x)) _ :=K.integrable_comp ht
 calc
   _= ∫ x, K (∫ y, F (x,y) ∂city _) ∂city _:= by unfold partitionZ; simp_rw [E.out]; rfl
   _= K (∫ x, (∫ y,F (x,y) ∂city _) ∂city _):=K.integral_comp_comm ht.integral_prod_left -- tune implicit order
   _= ∫ z, K (F z) ∂(city _).prod (city _):=by rw [K.integral_comp_comm ht,integral_prod F ht]
   _= ∫ y,(∫ x, K (F (x,y)) ∂city _) ∂city _:= integral_prod_symm _ hp
   _= _:=by
     unfold partitionZ; apply integral_congr_ae; apply Eventually.of_forall; intro y; dsimp only [F]; change (∫ x, beamL (mid m B) _ ∂city _)=beamZ (mid C B) (denZ R' P A' y); simp_rw [relay_v E]; rw [integral_smul_const]; have hk:= (E.pays).integrable y.1; rw [city]; rw [integral_prod]; simp only [integral_const, probReal_univ,one_smul,E.pays.total,one_smul]; rfl
     exact hk.comp_fst _
include E
end YM.CF.Scree
