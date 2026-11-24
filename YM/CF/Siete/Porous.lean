import YM.CF.Siete.Letters
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Skye Scree Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n j l:ℕ}{K M' H C Q b v a ε r u R x:ℝ}{c f:Side}{L:Side}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{P B:BudgetPoint}{X X':Support (More f)}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]
local notation "G"=>SU.group
section P
variable (M:Museum F x A X' Y I) (T:Tube G S) (V:Pane c)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(N:Pane f)(Z:LogArray G (Active A x F))(g:Seat c→SU.E)(e:Bond (More f))
local notation "o'" => S.ratio.parent e.1
local notation "Z'"=> recent T β k q d l N Z
abbrev hail (h: tangD c): Echo G (More c) (More f):=(sonic T M β k q d l N Z g e.1 V h,sonic T M β k q d l N Z g e.1 V 0)
local notation "δ"=>sonic T M β k q d l N Z g e.1 V
local notation "V'"=> hail M T V β k q d l N Z g e
local notation "z"=>reply T F x k g e
lemma contacts {t:Teller G}(hT:Act T F x k n v Q)(W:Folio.Bulletin x t T)(p:Mom.needed X' e)(b:Canvas P o' (Heir.reach x) V g n a) (hv:ContinuousAt V' 0)(he:‖V' 0‖ < v): ∀ᶠ w in 𝓝 (0:tangD c), Z' (increment V w) e= SU.group.lieExp (z (V' w))*Z' V e:=by
 have pp:= mem_union_left (inspected X'\ X') p.1; have hx:e.1∈ inspected X':= mem_union_left _ p.1; have hy:e.1+step e.2 ∈ inspected X':=mem_union_left _ p.2
 have ht: Tendsto (increment V) (𝓝 0) (𝓝 V):=by
    have he : Continuous (increment V):=by unfold increment; fun_prop
    simpa using he.tendsto (0:tangD c)
 filter_upwards [hv.norm.eventually (gt_mem_nhds he), ht.eventually b.seen] with u hu hp
 rw [recent_p T M β k q d l N Z _ _ hx hy,recent_p T M β k q d l N Z V _ hx hy]; unfold hail sonic at *; rw [Work.G07.at_zero_increment] at hu ⊢
 exact M.relative_read _ 1 W hT hx hy (M.asks_origin p.1) (by rw [separation_self]; omega) _ _ N hp b.seen.self_of_nhds hu.le
-- stage estimates with anchors. hV global P threshold small s := loom
local notation "s"=> loom P (Heir.reach x) b
local notation "zQ" => sphereQ V o' (Heir.reach x) g
lemma pierOne (o:Seat f)(h:Matins T F B.power u M')(p:Nut P V o' (Heir.reach x) n a b r g)(hn:j=1)(hu: j ≤ n)(ht:P.power=B.power)(hx:P.threshold ≤ 2*B.threshold)(hM:1 ≤ M')(w:Fin j→tangD c)(he:∀ i,P.dirBound (S.ratio.parent o) (w i)): ‖woody T F (iteratedFDeriv ℝ j zQ 0 w) e‖≤ M'*(b*2)*Lyre.width B o e:=by
 subst j
 let H(i:Bond (More c)):= Lyre.width P (S.ratio.parent o) i; have ha:=p.hC.trans p.hQ
 refine (h.stage _ _ o (t:=b*(2*B.threshold)) ?_ ?_).trans_eq ?_
 · have ht:=B.threshold_pos; positivity
 · intro i; rw [←ht]; by_cases v:separation o' i.1≤ Heir.reach x; swap; · rw [berth p.toCanvas i (not_le.mp v) w,norm_zero]; have ht:=B.threshold_pos; exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (spine_pos ..).le
   have hy:=post_jet p.toCanvas i r b ((p.toCanvas.paid p.hC).trans p.ht) p.hj v _ w he hu 0 rfl; rw [pow_one] at hy -- tactic dependent bug
   exact hy.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (spine_pos ..).le) (zero_le_one.trans ha)).trans_eq (mul_assoc ..).symm)
 unfold Lyre.width spine; ring
lemma step_hi (p:Nut P V o' (Heir.reach x) n a b r g)(hx:s ≤ 1)(hu:2 ≤ j)(hv:j≤n)(w:Fin j→ tangD c)(he:∀ i,P.dirBound o' (w i)): ‖iteratedFDeriv ℝ j zQ 0 w‖≤ s^2:=by
 have hy:=p.hC.trans p.hQ; have ht:=P.threshold_pos; have hg:0 ≤ s:=by unfold loom; positivity
 refine (pi_norm_le_iff_of_nonneg (sq_nonneg s)).mpr (fun i=> ?_)
 by_cases l:separation o' i.1≤ Heir.reach x; swap; · rw [berth p.toCanvas i (not_le.mp l) w,norm_zero]; positivity
 have hh:= post_jet p.toCanvas i r b ((p.toCanvas.paid p.hC).trans p.ht) p.hj l o' w he hv 0 rfl
 let h':= P.threshold*(1+(Heir.reach x:ℝ))^P.power
 calc
   _ ≤ b^j*h'^j:= hh.trans (mul_le_mul (le_self_pow₀ hy (by omega)) (pow_le_pow_left₀ (Lyre.width_pos ..).le (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0≤ (1+(separation i.1 o':ℝ))) (add_le_add_right (Nat.cast_le.mpr ((separation_comm i.1 o').le.trans l)) _) _) ht.le) j) (pow_nonneg (Lyre.width_pos ..).le _) (by positivity)) -- tune
   _ = s^j :=by unfold h' loom; rw [←mul_pow, ← mul_assoc b]
   _ ≤ s^2 := pow_le_pow_of_le_one hg hx hu
lemma priceZ (o: Seat f)(ho:o∈X)(hb:e.1∈inspected X)(h:Matins T F B.power u M')(p:Nut P V o' (Heir.reach x) n a b r g)(hn:0<j)(hu:j ≤ n)(ht:P.power=B.power)(hx:P.threshold ≤ 2*B.threshold)(hM:1 ≤ M')(hq:s ≤ 1)(w:Fin j→tangD c)(he:∀ i,P.dirBound (S.ratio.parent o) (w i)): ‖woody T F (iteratedFDeriv ℝ j zQ 0 w) e‖ ≤ M'*(b*2)*Lyre.width B o e + M'*s^2*heft n X P B:=by
 have hy:=p.hC.trans p.hQ; by_cases hj:j=1; · refine (pierOne T V g e o h p hj hu ht hx hM w he).trans (le_add_of_nonneg_right (by positivity [heft_one n X P B]))
 have hz:=rise_i j (step_hi V g e p hq (show 2 ≤ j by omega) hu) w he
 let C:= s^2*heft n X P B; have hp:0 ≤ C:= by unfold C; positivity [heft_one n X P B]
 have hs : spine B.power e.1 e.1=1:=spine_self ..
 have hr: ‖iteratedFDeriv ℝ j zQ 0 w‖ ≤ C:= hz.trans ((mul_le_mul_of_nonneg_right (heft_bounds S ho hb hu) (sq_nonneg _)).trans_eq (mul_comm ..))
 have hh:=h.stage (iteratedFDeriv ℝ j zQ 0 w) e e.1 hp (fun i=> (norm_le_pi_norm _ _).trans (hr.trans (le_mul_of_one_le_right hp (spine_one ..))))
 unfold C at hh; rw [spine_self,mul_one,←mul_assoc] at hh; exact hh.trans (le_add_of_nonneg_left (by positivity [Lyre.width_pos B o e]))
end P
end YM.CF.Siete
