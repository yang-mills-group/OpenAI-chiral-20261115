import YM.CF.Hive.Med
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye MeasureTheory Jet
variable {N B m L:Side}{j k:ℕ}{z K v a b d c e H t:ℝ}
local notation "N₀"=>CSide m B
variable {S:Seal (Skye.Seat (CSide m B))}{P': Stent (CSide m B)}{A:Ids (CSide m B)}
-- meas exterior. tags at rates long. chip
lemma mossB(S: Seal (Skye.Seat N)):Measurable (chip (N:=N) S):=by
 let g(x: Ids N):= greet S (priorP x); have ht:Measurable g:=(mastM _).comp primeV
 apply mealM (F:=g) (G:=fun i x=>(x i).2.1); exact fun i=>ht (measurableSet_singleton _); exact fun i=>measurable_fst.comp (measurable_snd.comp (measurable_pi_apply _))
lemma mornP(s:Sweep N₀): Measurable fun x: Castle m B e S × Ids N₀=> moveD (S:=S) (e:=e) s x.2 x.1:=by
 have hf: Measurable (frameP (n:=N₀)):=measurable_pi_lambda _ fun i=> measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))
 
 let D(x: Castle m B e S × Ids N₀)(i:Bool): Skin m B:= x.1.val i
 let F(x: Castle m B e S × Ids N₀):Site (More (CSide m B))→ E:= frameP x.2
 have ht : Measurable F:=hf.comp measurable_snd
 have he:Measurable D := measurable_subtype_coe.comp measurable_fst
 have hz:Measurable (fun x: (Skye.Seat N₀→ E)×Skin m B=> (Lattice.gauge x.1 x.2:Skin m B)):=by apply Continuous.measurable; apply continuous_pi; intro i; unfold Lattice.gauge; fun_prop
 have hk(i:Bool): Measurable (fun x: Castle m B e S × Ids N₀=> (gauge (F x) (D x i):Skin m B)):=by
    have hx :Measurable (fun x: Castle m B e S × Ids N₀=> D x i):= (measurable_pi_apply i).comp he
    let V(x):= (F x,D x i); have h:Measurable V:= ht.prodMk hx
    change Measurable ((fun x:(Skye.Seat N₀→ E) × Skin m B=>(Lattice.gauge x.1 x.2:Skin m B)) ∘ V)
    exact Measurable.comp hz h
 have hd : Measurable (fun x: Castle m B e S × Ids N₀=> ((moveD s x.2 x.1).val : Bool→ Skin m B)):=measurable_pi_lambda _ fun i=> (revM s).measurable.comp (hk i)
 exact Measurable.subtype_mk hd

lemma moteQ (s:Sweep N₀){X:Axx (Skye.Seat N₀) (Single N₀) (Castle m B e (actS s S))}(i:DeckU X.2.1)(p:fits (landX k K (actS s S) e) (home_n _) (actS s S) X): Measurable (fun x: Castle m B e S × Ids N₀=> (charm S s x.2 X i).2.2.1 x.1):=by
 let b:= χ s⁻¹; have hf:Continuous (cSignX b):=by unfold cSignX; split; exact continuous_star; exact continuous_id -- tune
 exact ((jiveM s⁻¹ X.2.1 i).comp measurable_snd).smul (hf.measurable.comp (p.2.2.2.2.cont.measurable.comp (mornP s)))
variable (V:∀ S: Seal (Skye.Seat (CSide m B)), Lend m B e S)
abbrev Shred (R:Seal (Skye.Seat N₀)):= Σ i:(V R).slots, DeckU ((V R).crew i).2.1
variable (S)
def sumW (s:Sweep N₀)(U:Ids N₀)(i: Shred V (actS s S)): Axx (Skye.Seat N₀) (Single N₀) (Castle m B e S):= charm S s U ((V (actS s S)).crew i.1) i.2
lemma hols (x:Castle m B e S)(U: Ids N₀)(X:Stent N₀):let s:=chip S U
 hula V S x U X=∑ j: Shred V (actS s S), if (sumW S V s U j).1∈ X then vowC (sumW S V s U j) x else 0:=by
 intro s; rw [hula,map_sum,Fintype.sum_sigma]; refine sum_congr rfl fun j _=> ?_ -- tune let
 let Q:=(V (actS s S)).crew j; have hg(i:DeckU Q.2.1): (sumW S V s U ⟨j,i⟩).1=actS s⁻¹ Q.1:= rfl
 change mallC S U (if actS s⁻¹ Q.1 ∈ X then vowC Q (strideH S U x) else 0)=∑ k:DeckU Q.2.1,if actS s⁻¹ Q.1 ∈ X then vowC (charm S s U Q k) x else 0
 by_cases h:actS s⁻¹ Q.1∈ X; swap
 · simp only [if_neg h,map_zero,sum_const_zero]
 simp only [if_pos h]; exact vivX U S Q x
variable {o: Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}{I:Aim (CSide m B)}{M: Male}
-- transfers conditional Deck rank to all<br>
lemma swing_a(s:Sweep N₀)(U: Ids N₀)(p:ShiftD k H K e S U s)(h:Grove (terr _) S)(u:Vista P M I V k K ((Fintype.card Play:ℝ)*z) t a): (∀ i:Shred V (actS s S),fits (landX k H S e) (home_n _) S (sumW S V s U i)) ∧
 (∑ i: Shred V (actS s S), hireC a z S (sumW S V s U i)) ≤ Real.exp (t*S.card*((Fintype.card Play:ℝ)*z)^2):=by
 let R:=actS s S; have hp:=u.carry R (grove_t S s h); refine ⟨fun i=> repay _ _ _ _ _ p (hp.1 _),?_⟩
 rw [Fintype.sum_sigma]; rw [←show R.card=S.card from Finset.card_map _]; exact le_trans (sum_le_sum fun i _=> le_of_eq (far_p S s U _ (hp.1 i).1 z a)) hp.2.1
lemma phase_u(s:Sweep N₀)(U:Ids N₀)(A:Finset (Shred V (actS s S)))(V':Ids N₀){u:Seal (Skye.Seat N₀)}(h:Grove (terr _) S)(p: Vista P M I V k K b t a)(x y:Castle m B e S)(he:∀ i∈A,(sumW S V s U i).1 ⊆ u)(g:Set.EqOn U V' u)(hz:∀ i,Agrees u (x.val i) (y.val i)): ∀ i ∈ A, vowC (sumW S V s U i) x=vowC (sumW S V s V' i) y:=by
 let Q:=actS s S; intro i l; let W:=(V Q).crew i.1; exact congrArg (fun t:ℂ=> t • drum (castJ s⁻¹ W.2.1 i.2)) (appear S s U W V' i.2 x y ((p.carry Q (grove_t _ _ h)).1 _) (g.mono (Finset.coe_subset.mpr (he i l))) (fun j=>agrees_mono (hz j) (he i l)))
end YM.CF.Hive
