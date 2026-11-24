import YM.CF.BPress.Lilac.Shell
/- π integration arrays. ${Tiny first difference bound. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Born Peel.Along Mosaic
variable {m s N:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u b:ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Stripe
variable (B0:Born A R X Y) (P:Edition Y)(L:Passports Y T G h P p3 q d ε t v)(F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)(Φ:RightsC X R H b)(g:Seer H R X k) (a:Fast H.y) (r:ℕ)
local notation "A₁"=> ΓStage F Q
-- long contribution when not Tiny AND currency.Haus
abbrev paysL (x:Visit A R H)(i:Tenor η) := if Tiny A X r i.2 then 0 else δRest A X.W.M scaffold (fun i=>P.op i ((A₁) (party A R H x))) i
abbrev arts (x:Visit A R H)(i:Tenor η):= P.op i ((A₁) (party A R H x))
-- soft.Act $first-difference charge: no extra Mark-only budgets. unit. off if no root.
def start0 (x: Visit A R H)(i: Tenor η) : ℂ:= if Tiny A X r i.2 then if plan A R i.1∈ vicinity H x.val then 0 else arts P F Q x i-P.op i (B0.H₁ (chip x.val (plan A R i.1))) else 0
def mie (u:ℝ)(b:Pledge)(x:ℕ):= u * (Real.exp (-(b.rate/2*x)) * b.price) -- tune cast
variable {P B0 F Q r}
include L Φ g a
private lemma mayF (i:Tenor η) : Measurable fun x: Visit A R H=>arts P F Q x i:= (L.measure i).comp ((Γ_m F Q).comp (party_meas a)) -- tune Q implicit
private lemma hut (h:b≤p3.rate/2)(r:ℕ): Cash scaffold (fun i: Tenor η=> if (¬Tiny A X r i.2∧ Wanted A X i.2) then P.opfee i else 0) b (Real.exp (-(p3.rate/2*r))* p3.price):=by
 let w(i:Tenor η):= P.opfee i; let d:=Real.exp (-(p3.rate/2*r)); refine ⟨fun i=>ite_nonneg (L.cruise.pos i) le_rfl,fun x=>budget_mono (budget_scale (Real.exp_pos _).le (L.cruise.hits x)) (fun i=>?_ ) (fun i=>?_ )⟩; · unfold Ledger.score; refine ite_nonneg (mul_nonneg (Real.exp_pos _).le (ite_nonneg (L.cruise.pos _) le_rfl)) le_rfl
 unfold Ledger.score; split
 next hz=>
   dsimp only; split; next t=>
    apply le_trans _ (mul_assoc d _ _).le; refine mul_le_mul_of_nonneg_right ?_ (L.cruise.pos _)
    change _ ≤ Real.exp _*Real.exp _; rw [← Real.exp_add]; apply Real.exp_monotone; have ht:r < i.2.card:=lt_of_not_ge (fun h=>t.1 ⟨t.2,h⟩); have hz: (r:ℝ)≤ (scaffold i).card:= Nat.cast_le.mpr ht.le; nlinarith [p3.pos]
                                                     -- indent
   next u=> rw [mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (L.cruise.pos i))
 next h=> rw [mul_zero]
theorem earns1(h:b≤p3.rate/2)(r:ℕ): Lift (mie (MicCost R X B b) p3 r) (fun x:Visit A R H=> ∑ i:Tenor η,paysL P F Q r x i):=by
 let U:= Φ; refine mirror Φ (hut L Φ g a h r) (fun i w=>?_) (fun i x=>?_) (fun i=>?_)
 · split at w; next t=> obtain ⟨p,e⟩:= L.point i w; let h:=Abyss.foot A X.W.M p t.2; refine ⟨h,FeeT.general Φ g.charter.port p h (fun S G x y q=>?_)⟩; unfold paysL; rw [if_neg t.1,if_neg t.1]; unfold δRest; simp only [if_pos (show currencyT A X.W.M (scaffold i) from t.2)]; exact L.view _ _ _ (hasP g G q F Q) -- tune
   next h=>contradiction
 · unfold paysL δRest; by_cases p:Tiny A X r i.2; simp only [p,↓reduceIte, not_true_eq_false, false_and,norm_zero,le_refl]; by_cases t:Wanted A X i.2; rw [if_neg p,if_pos (show currencyT A X.W.M (scaffold i) from t), if_pos ⟨p,t⟩]; exact L.known i _; rw [if_neg p,if_neg (show ¬currencyT A X.W.M (scaffold i) from t),if_neg (fun h=>t h.2),norm_zero] -- tune
 unfold paysL δRest; split_ifs; exact measurable_const; exact mayF L Φ g a i; exact measurable_const -- tune
lemma startKnow (i:Tenor η)(p0:P.opfee i≠0)(v:ShortP X H R r)(q:Tiny A X r i.2) (x y: Visit A R H) (h:Peek H (Peel.stem (plan A R i.1) 40) x.val y.val): start0 B0 P F Q r x i=start0 B0 P F Q r y i:=by
 let U:=plan A R i.1; have ht:= L.point i p0; have he(x:Visit A R H)(w):start0 B0 P F Q r x i=w→True:=fun _=>trivial; unfold start0; simp_rw [if_pos q]; by_cases h':plan A R i.1∈ vicinity H x.val; swap; · obtain ⟨b,k⟩:= visits_t x h' y h (stem_mid U (by norm_num)); rw [if_neg h',if_neg b,k]; apply congrArg (·- _); exact (L.view i _ _ (hasP g (shortBody (Abyss.foot A X.W.M ht.1 q.1) ht.1 q.2 v g.charter.port i.1 ht.2 (by norm_num : 7≤40)) h F Q))
 rw [if_pos h', if_pos (_:plan A R i.1∈ vicinity H y.val)]; exact Classical.byContradiction fun b=> (visits_t y b x h.swap (stem_mid U (by norm_num))).1 h'
variable (p:0<c)(d1:shellQ c≤d)(V:X.qX<q) (t':ShortP X H R r)
include p d1 V t'
lemma shelters (i:Tenor η) (x:Visit A R H)(T:Tiny A X r i.2)(w:P.opfee i≠0)(k:plan A R i.1∉ vicinity H x.val): ‖arts P F Q x i-P.op i (B0.H₁ (chip x.val (plan A R i.1)))‖≤ P.opfee i * shadow r c:=by
 let z:=chip x.val (plan A R i.1); let y:= B0.H₁ z; have ht:=L.point _ w; have he:=climbS B0 F Q t' ht.1 T.2 (Abyss.foot A X.W.M ht.1 T.1) x ht.2 k p
 apply L.surge i _ y (B0.heG _) _ he.1 (mul_pos clip_p p) d1 he.2 (shadowP p.le r); apply Stage.travel A R X (Reference z A) ∅ 1 (B0.ideal z) _ V -- tune
lemma earns2 (v:b≤p3.rate): Lift (MicCost R X B b * (shadow r c*p3.price)) (fun x=>∑ i,start0 B0 P F Q r x i):=by
 let c'(i:Tenor η):=if Tiny A X r (scaffold i) then shadow r c*P.opfee i else 0; let hc:0≤ shadow r c:=(mul_pos clip_p p).le.trans (shadowP p.le r); let f(i)(x):=start0 B0 P F Q r x i; let g'(i):= mul_nonneg hc (L.cruise.pos i); refine mirror Φ (((L.cruise.chill v).scale (shadow r c) hc).subs (c:=c') (fun i=> ite_nonneg (g' i) le_rfl) (fun i=> by unfold c'; split; rfl; exact g' i)) (fun i u=>?_) (fun i x=>?_ ) (?_)
 · unfold c' at u; split at u; next t=>
      have p:=right_ne_zero_of_mul u; have ht:=L.point i p; let v:= Abyss.foot A X.W.M ht.1 t.1; exact ⟨v,_, FeeT.smallBody Φ g.charter.port t' t.2 ht.1 v i.1 ht.2 (startKnow L Φ g a i p t' t)⟩
   next t=> contradiction
 · change ‖f i x‖≤ c' i; unfold f start0 c'; split; next T=>
      split; next h=> rw [norm_zero]; exact g' i
      next h=> by_cases h':P.opfee i=0; · unfold arts; simp only [due_iff L _ h',sub_self,norm_zero,h',mul_zero,le_refl]; -- tune
               exact (shelters L Φ g a p d1 V t' i x T h' h).trans_eq (mul_comm ..) -- tune
   next h=> rw [norm_zero]
 intro i; change Measurable (f i); unfold f start0; split; next p=> refine Measurable.ite (measurable_subtype_coe (vicinity_m (H:=H) _)) measurable_const ((mayF L Φ g a _).sub ?_); exact (measurable_of_countable (fun z=>P.op i (B0.H₁ z))).comp ((chip_m _).comp measurable_subtype_coe)
 next h=> exact measurable_const
end Stripe
end YM.CF.BPress.Lilac
