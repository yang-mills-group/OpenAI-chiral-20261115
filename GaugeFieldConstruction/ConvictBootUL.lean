import GaugeFieldConstruction.TenuredBootUL
import GaugeFieldConstruction.TamarBootUL
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set MeasureTheory Measure Complex
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}
noncomputable def AlumUL : E4 × Points n →L[ℝ] Points (n+1) := {toFun:=fun p=>cons p.1 p.2, map_add':= by rintro x y; apply PiLp.ext; intro i; refine Fin.cases ?_ ?_ i <;> simp [cons], map_smul':= by intro c x; apply PiLp.ext; intro i; refine Fin.cases ?_ ?_ i <;> simp [cons], cont:=alabasterYL} -- sty tune
variable (a:Axis)(p:Points n)(b:Bulb)(k:Fin n)(F:Points (n+1)→ℂ)(m:ℕ)(e:ContDiffOn ℝ m F (conf (n+1)))
include e
lemma wrapConUL: ContDiffOn ℝ m (raysCostYL b a F) (CellsUL b k):=by
 let X:= E4 × Points n; let V := VestHYL b a
 let Y (p:X):=D (basis a) b.f p.1 • F (AlumUL p)
 refine convolveUL Y (CellsUL b k) (BreathingMars b k) V (vestKYL a b) m (fun x _ y s=> ?_) (fun x u y=>?_)
 · unfold Y; simp only [show D (basis a) b.f y=0 from image_eq_zero_of_notMem_tsupport s,zero_smul]
 by_cases h:y∈V
 · have hp:=show AlumUL (y,x)∈ conf (n+1) from RoomMars _ _ _ u _ (Bulb.cone b a h)
   have ht:ContDiffAt ℝ m (F∘AlumUL) (y,x):=((e _ hp).contDiffAt ((conf_open _).mem_nhds hp)).comp (y,x) (AlumUL.contDiff.contDiffAt)
   have he:ContDiffAt ℝ m (D (basis a) b.f) y:=((b.LED a).d.of_le (show (m:WithTop ℕ∞)≤∞ from by exact_mod_cast (le_top (a:=(m:ℕ∞))))).contDiffAt
   exact (ContDiffAt.comp (f:=fun t:X=>t.1) (y,x) he contDiffAt_fst).smul ht
 refine (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq ?_
 filter_upwards [continuousAt_fst (p:=(y,x)) |>.tendsto ((vestKYL a b).isClosed.isOpen_compl.mem_nhds h)] with z w
 exact (show Y z=0 by unfold Y; rw [show D (basis a) b.f z.1=0 from image_eq_zero_of_notMem_tsupport w,zero_smul])
omit e
variable {X:Type*} (J:Axis→Axis→X)
abbrev ChefUL := ∀ n, (Fin n→X)→Points n→ℂ
variable (Q: ChefUL (X:=X))
noncomputable abbrev ovensUL (a:Axis)(F:Fin n→X)(i:Axis):= Q (n+1) (Fin.cons (J i a) F)
abbrev GiftUL(k:Fin n)(b:Bulb): Prop:=
 (∀ (a:Axis)(p:Points n)(r:ℝ)(F:Fin n→X), calmYL k a r p b→ (Q n F (ledgeYL k a r p 1) - (Q n F p + r • ∑ j:Axis, ScrollOpYL a p b j k r (ovensUL J Q a F j)))=0) ∧ (∀ (a:Axis)(p:Points n)(F:Fin n→X), BreatherMars b k p→(∑ j:Axis,∑ i:Axis,raysCostYL b i (ovensUL J Q j (Function.update F k (J j a)) i) p)=0)
abbrev PathUL:=∀ n (x:Points n),x∈conf n→∀ k: Fin n, ∃ b:Bulb,BreatherMars b k x∧GiftUL J Q k b
variable (B:Fin n→Bulb)(h:∀ k, BreatherMars (B k) k p)(t:∀ k, GiftUL J Q k (B k))
variable (F':Fin n→X)(w:∀ n F,ContinuousOn (Q n F) (conf n))
include w
noncomputable abbrev WaltzUL(i:RockUL n):= ovensUL J Q i.2 F'
include h t
lemma CoveUL : HasFDerivAt (Q n F') (SoUL (fun i=>silkUL B (WaltzUL J Q F') i p) Finset.univ) p:= UrnUL p B _ _ h (fun i x r u=>sub_eq_zero.mp ((t i.1).1 i.2 x r _ u)) (fun i j=> w _ _)
lemma FlueUL (k:Fin n): D (mirDirYL k a) (Q n F') p=∑ j:Axis, raysCostYL (B k) j (ovensUL J Q a F' j) p:=by
 unfold D; rw [(CoveUL p J Q B h t F' w).fderiv]; exact ZipProcUL _ (k,a)
omit h t
variable (H:PathUL J Q)
include H
lemma pureSmUL : ContDiffOn ℝ m (Q n F') (conf n):=by
 induction m generalizing n with
 | zero=> simpa using w _ F'
 | succ m ih=>
   rw [Nat.cast_add_one,contDiffOn_succ_iff_fderiv_of_isOpen (conf_open _)]
   refine ⟨fun x hx=> ?_,by simp, fun x hx=>?_⟩
   · choose B u e using H n x hx; exact (CoveUL x J Q B u e F' w).differentiableAt.differentiableWithinAt
   choose B u e using H n x hx
   let G:=WaltzUL J Q F'
   have hp(i:RockUL n):ContDiffAt ℝ m (silkUL B G i) x:= by
     let Y:= fun (j:Axis) (z: Points n)=> raysCostYL (B i.1) j (G i j) z
     exact ContDiffAt.sum fun j (_ : j∈(Finset.univ:Finset Axis))=> (show ContDiffAt ℝ m (Y j) x from (((wrapConUL j (B i.1) i.1 _ m (ih _)) x (u i.1)).contDiffAt ((BreathingMars _ _).mem_nhds (u i.1)))) -- tune n arguments
   have he(i:RockUL n): ContDiffAt ℝ m (fun y=> ContinuousLinearMap.toSpanSingleton ℝ (silkUL B G i y) ∘L CξUL i) x:= (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).toContinuousLinearEquiv.contDiff.contDiffAt).comp x (hp i)).clm_comp contDiffAt_const -- tune
   have ht: ContDiffAt ℝ m (fun y=>SoUL (fun i=>silkUL B G i y) Finset.univ) x:= ContDiffAt.sum (fun i _=>he i)
   refine (ht.congr_of_eventuallyEq ?_).contDiffWithinAt
   have hu:∀ᶠ y in 𝓝 x,∀ i:Fin n,BreatherMars (B i) i y:= eventually_all.mpr fun i=> (BreathingMars _ _).mem_nhds (u i)
   exact hu.mono fun y v=> (CoveUL y J Q B v e F' w).fderiv
lemma PureUL: ContDiffOn ℝ ∞ (Q n F') (conf n):= contDiffOn_infty.mpr fun m=> pureSmUL m J Q F' w H -- tune
lemma SolidUL : ∑ i:Axis, D (mirDirYL k i) (Q n (Function.update F' k (J i a))) p=0 ∨ p∉conf n:=by
 by_cases z:p∈conf n; swap; · exact Or.inr z
 left; choose B u e using H n p z
 simp_rw [FlueUL _ p J Q B u e _ w k]; exact (e k).2 a p F' (u k)
#print axioms PureUL
end YM.GaugeFieldConstruction.Fathom
end
