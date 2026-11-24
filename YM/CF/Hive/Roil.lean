import YM.CF.Hive.Paths
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
variable {N B m L:Side}{S: Seal (Skye.Seat (CSide m B))}{j k:ℕ}{v a b d c e H t:ℝ}
local notation "N₀"=> CSide m B
lemma pulley (n:ℕ) (D:ℝ)(p:1≤D): ∃ K:ℝ,D≤ K∧ ∀ {m B:Side}{e:ℝ}(S: Seal (Skye.Seat (CSide m B)))(X:Ids (CSide m B))(s:Sweep (CSide m B)), ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (V:Set E)(F:E→ Castle m B e S), (dealX (m:=m) n D S e).test E V F → (dealX n K (actS s S) e).test E V ((fun x=>pullT s (pullF S (frameP X) x))∘ F):=by
 obtain ⟨K,hK,H⟩:= Spire.tutor D n p; refine ⟨K,hK,fun {m B e} S X s E _ _ _ V F hp y hy i=> ?_⟩
 let g:=frameP X
 let x(v:E):=Lattice.gauge g ((F v).val i)
 have ht:TransK n x y D:=by
    intro j; have he:= hp y hy i j; let P:= fund (g j.1); let T:= fund (g (j.1+Lattice.step j.2))⁻¹; -- tune notation
    let Q: Op SU.F→L[ℝ] Op SU.F:=({toFun:=fun w=> P*w*T,map_smul':=fun i j=>by simp,map_add':=fun i j=>by simp [mul_add,add_mul]}: Op SU.F→ₗ[ℝ] Op SU.F).toContinuousLinearMap
    have hx: ‖Q‖≤1:=by
       apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; change ‖P*x*T‖ ≤ _; have hp := SU.fund_U (g (j.1+step j.2))⁻¹
       exact le_of_eq ((CStarRing.norm_mul_coe_unitary (P*x) (⟨T,hp⟩)).trans (CStarRing.norm_coe_unitary_mul ⟨P,SU.fund_U _⟩ x)) -- tune order
    refine ((he.linear Q hx).mono (one_mul D).le).germ ?_ ; exact Filter.Eventually.of_forall fun v=> rfl
 let f(_:E)(_: Site (More (CSide m B))) := apex; exact (H (CSide m B) _ _ E x y f ht (fun i=>allows_const y ((vote_unit apex).le.trans p))).1
lemma pSign (u: Bool)(F: Castle m B e S→ ℂ) {X:Seal (Skye.Seat N₀)} (p:Acorn.Pro (landX j H S e) X F a): Acorn.Pro (landX j H S e) X (cSignX u ∘ F) a:=by
 cases u; exact p; refine ⟨p.pos,p.travel,continuous_star.comp p.cont,fun y=>(show ‖_‖=‖F y‖ from norm_star _).trans_le (p.sumline _),fun x y h=> congrArg star (p.reads x y h), fun E _ _ _ W f K t x hx=>?_⟩
 exact ((p.plot _ _ f K t x hx).linear Complex.conjCLE.toContinuousLinearMap (show ‖Complex.conjCLE.toContinuousLinearMap‖≤1 by simp)).mono (one_mul _).le
abbrev moveD (s:Sweep N₀)(X: Ids N₀)(Y:Castle m B e S):Castle m B e (actS s S):=pullT s (pullF S (frameP X) Y)
abbrev ShiftD (n:ℕ)(v d e:ℝ)(S: Seal (Skye.Seat N₀))(X:Ids N₀)(s:Sweep N₀):Prop:=∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:Set E)(F:E→Castle m B e S),(dealX n v S e).test E V F→(dealX n d (actS s S) e).test E V (moveD s X∘ F)
lemma ferryG(T:Seal (Skye.Seat N₀))(A Z:Ids N₀)(s:Sweep N₀)(U V:Castle m B e S)(hp:Set.EqOn A Z (actS s⁻¹ T))(h:∀ i, Lattice.Agrees (actS s⁻¹ T) (U.val i) (V.val i)): (farmX (actS s S) e).rel T (moveD s A U) (moveD s Z V):=by
 intro i; apply flashD s; rw [show Finset.map (boxA s).toEmbedding T=actS s⁻¹ T from ?_]; swap; · unfold actS; rw [sitU]; rfl
 exact tied _ _ _ _ _ (h i) (fun i l=> by unfold frameP; rw [hp l])
lemma move_c (s:Sweep N₀)(x:Ids N₀):Continuous (moveD (S:=S) (e:=e) s x):=by
 apply Continuous.subtype_mk; apply continuous_pi; intro i
 let U(w:Castle m B e S):=w.val i
 have ht:Continuous U:= (continuous_apply _).comp continuous_subtype_val
 apply (revM _).comp; refine (continuous_pi fun j=>?_ : Continuous (fun v=> gauge (frameP x) (U v))); unfold Lattice.gauge; fun_prop
lemma ferry (A:Ids N₀)(s:Sweep N₀)(l:ShiftD k v H e S A s){F: Castle m B e (actS s S)→ℂ}{X:Seal (Skye.Seat N₀)} (p:Acorn.Pro (landX k H (actS s S) e) X F a): Acorn.Pro (landX k v S e) (actS s⁻¹ X) (F ∘ moveD s A) a:=⟨p.pos,fun q=>grove_t _ _ (p.travel q),p.cont.comp (move_c ..),fun y=>p.sumline _,fun x y h=> p.reads _ _ (ferryG X A A s _ _ (fun _ _=>rfl) h), fun E _ _ _ V h F r x g=> p.plot E V h _ (l E V F r) x g⟩
end YM.CF.Hive
