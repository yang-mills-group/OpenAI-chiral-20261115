import YM.SU5.Regis.Easel
import YM.SU5.Circuit.Lark
import GaugeFieldConstruction.Rods
/-! # Sensing on pulled chart. Thole lemma combines angular width, pane gate, boarded projection. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 45000
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis Regis.Head ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X V D:Dir G n}{R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J: ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort Gleam.clocks
open CF.Rue (FleetS shoreK)
open CF.Scree (pingS)
variable (s: Signed) {K:Support n}{W D':Flaws n}{E:T.Slice G}
abbrev signX (x:Support n)(s:Signed)(t:Site n):= x.image (affine s t)
-- Fare
lemma hub_ok (Light:LightM r W D' m (signX K s 0))(pW: W=misdemean t U)(hp:FleetS t U) : pingS t K (pull s 0 U):=by
 have h:FleetS t (pull s 0 U):= by intro f h; exact hp (Face.send s 0 f) ((Face.send_price U f s 0 _ G.chord_inv (fun i j=> G.chord_conj j i)).symm.trans h)
 apply (shoreK _ _ h _).1; apply disjoint_left.mpr; intro j tL x; let u:= affine s (0:Site n) j; have hv:u∈ flags t U:= by rw [← Work.H03.flags_send s 0]; exact mem_image_of_mem _ x -- tune
 obtain ⟨i,g,h⟩:= (flags_spec ..).mp hv; let z:= separation u i.1; have hz:z ≤ 2:=by unfold z; rw [separation_comm]; exact Work.E01.sep_touched i _ g
 have hx:hallBill m<z:= (Light u (mem_image_of_mem _ tL)).2 _ (by rw [pW]; exact mem_filter.mpr ⟨mem_univ _,h⟩)
 unfold hallBill Sequest at hx; omega
private lemma endsM (r:Ratio c n)(x:Step)(a:Site n)(j:Site c)(p:r.parent a=j)(q:r.parent (a+x.vec)=j): InHouse r j (x.used a):=by obtain ⟨i,j'|j'⟩:=x; exact ⟨p,q⟩; exact ⟨(by simpa [Step.used,Step.vec,sub_eq_add_neg] using q),(by simp [Step.used,p])⟩
lemma fare_W (Light:LightM r W D' m (signX K s 0))(h:TrustLogs X U r (grid_break r D') v) (e: Bond n)(p:e.1∈ K): G.chord ((pull s 0 U) e) ≤ v:=by
 let i:= affine s (0:Site n) e.1; let c:= r.parent i; let b:Step:= (posDir e.2).rotate s; have hg: InHouse r c (b.used i):= endsM r b i c rfl ((Light i (mem_image_of_mem _ p)).1.2 _ (by
    have hp:separation i (i+b.vec) ≤1:= by unfold b; rw [Step.vec_rotate,Step.vec_pos, show i+_ = affine s 0 (e.1+step e.2) from (by unfold i; simp [affine])]; unfold i; simpa only [affine,add_zero,separation_signed] using step_towards e.1 e.2
    unfold hallBill Sequest; omega))
 have hf:G.chord (U (b.used i)) ≤ v:= (h _ ⟨hg.1.symm ▸ (Light i (mem_image_of_mem _ p)).1.1,hg.1 ▸ hg⟩).2
 change G.chord (b.read _ i) ≤ v; unfold Step.read; split_ifs; · rw [G.chord_inv]; exact hf
 exact hf

/- Compass variables: an integer-oriented transported slot (paths including shift to face). Supports need not be enlarged in admission, only in P.Jekk. -/
structure Tick (n:Side) (G:Gauge) where
 o:Site n
 axis:RG.Slot
 i:G.ColorIndex
namespace Tick
variable (d:Tick n G)
-- one holonomy facet and color coordinate
abbrev raw (U: Config G n):ℝ:= d.axis.atSite U d.o d.i
abbrev faceZ (s:Signed):Cell n:= slotFace (skewSlot G d.axis s) (affine s 0 d.o)
def Compass (S:Support n) (k:ℕ):Prop:= d.o∈ S ∧ ∀ s:Signed,(skewSlot G d.axis s).length ≤ k ∧ (d.faceZ s).1 ∈ signX S s 0
lemma raw_cost (p₀: d.Compass K f) (p':W=misdemean t U)(Light:LightM r W D' m (signX K s 0)): |d.raw (pull s 0 U)| ≤ t:=by
 let a:=d.axis; let g:=d.o; let b:=d.faceZ s
 have ht:d.raw (pull s 0 U)=skewSig G d.axis s*((skewSlot G d.axis s).atSite U (affine s 0 d.o)) d.i:=by rw [raw,reflects]; rfl
 rw [ht,abs_mul,skewSq,one_mul]; let F:= (skewSlot G d.axis s).atSite U (affine s 0 d.o)
 have hy:Brisk r (grid_break r D') W (hallBill m) b.1:= Light b.1 (p₀.2 s).2
 apply (show |F d.i| ≤ ‖F‖ from by rw [←Real.norm_eq_abs]; exact PiLp.norm_apply_le F _).trans; unfold F; rw [atSite_path, Gauge.norm_adjoint]; apply (G.curvature_norm _).trans; apply le_of_not_gt; intro l
 have h:b∈ W:=by rw [p']; exact mem_filter.mpr ⟨mem_univ _,l⟩; -- tune
 have hp:= hy.2 b h; simp at hp
abbrev spinner (q:Clip) : Altar G n→ℝ:= fun x=> (Etch.river q (slotFace d.axis d.o) x) d.i
abbrev θSlot (q:Clip)(s:Signed) : Altar G n→ ℝ:=fun x=> skewSig G d.axis s * (Etch.river q (d.faceZ s) x) d.i
abbrev riverOne(q:Clip)(b:Cell n)(i:G.ColorIndex) : StrongDual ℝ (Altar G n):=(EuclideanSpace.proj i).comp (Etch.river (G:=G) q b).toContinuousLinearMap
lemma river_serve (Q:Support n)(b:Cell n)(i:G.ColorIndex)(h:b.1 ∈ Q) (x:Altar G n): |riverOne q b i x|≤(Real.sqrt q.direct)⁻¹ * bayColour Q x:=by
 change |(Real.sqrt q.direct)⁻¹*x (b,false,i)| ≤ _; rw [abs_mul, abs_of_pos (by have ht:= q.quadratic_pos; positivity :0<(Real.sqrt q.direct)⁻¹)]; apply mul_le_mul_of_nonneg_left _ (by have ht:=q.quadratic_pos; positivity)
 apply (sq_le_sq₀ (abs_nonneg _) (shade_b ..)).mp; unfold bayColour; rw [sq_abs, Real.sq_sqrt]; exact single_le_sum (fun i _=>sq_nonneg _) (mem_filter.mpr ⟨mem_univ _,h⟩)
 exact sum_nonneg (fun i _=>sq_nonneg _)
lemma river_norm (b:Cell n)(i:G.ColorIndex) : ‖riverOne q b i‖≤(Real.sqrt q.direct)⁻¹:=by
 let t:= (Real.sqrt q.direct)⁻¹; apply ContinuousLinearMap.opNorm_le_bound _ (by have ht:= q.quadratic_pos; positivity); intro x; rw [Real.norm_eq_abs]; change |_| ≤ _; apply (river_serve (Q:=univ) b i (mem_univ _) x).trans; apply mul_le_mul_of_nonneg_left _ (by have ht:=q.quadratic_pos; positivity)
 apply (sq_le_sq₀ (shade_b ..) (norm_nonneg _)).mp; unfold bayColour; rw [Real.sq_sqrt,EuclideanSpace.real_norm_sq_eq]; exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _=>sq_nonneg _)
 exact sum_nonneg (fun i _=>sq_nonneg _)
abbrev leadS (q:Clip)(s:Signed) : StrongDual ℝ (Altar G n):= (skewSig G d.axis s) • riverOne q (d.faceZ s) d.i
lemma leader (p:d.Compass K f)(x:Altar G n): |d.leadS q s x|≤ (Real.sqrt q.direct)⁻¹ * bayColour (signX K s 0) x:=by
 change |skewSig _ _ _ * (riverOne q (d.faceZ s) d.i x)| ≤ _; rw [abs_mul,skewSq,one_mul]; exact river_serve _ _ _ (p.2 s).2 _
lemma lead_θ (x:Altar G n) : d.leadS q s x=d.θSlot q s x:= rfl
lemma pays : ‖d.leadS q s‖≤(Real.sqrt q.direct)⁻¹:=by rw [leadS,norm_smul,Real.norm_eq_abs,skewSq,one_mul]; apply river_norm
lemma angle_S (Light:LightM r W D' m (signX K s 0))(p₀:d.Compass K f)(h:TrustLogs (V+D) U r (grid_break r D') v)(u:0≤ v)(t:v≤R.c)(p:f≤ m):
  |Real.sqrt β * d.raw (pull s 0 U)-d.θSlot q s (starOf B P r (grid_break r D') W m D β V)| ≤ Real.sqrt β * slotError R f v:=by
  let i:= affine s (0:Site n) d.o; let e:= skewSlot G d.axis s; let X:= grid_break r D'; let g:=e.atSite U i; let γ:=faceCurl (slotFace e i) (V+D)
  have he: Brisk r X W (hallBill m) i:= Light i (mem_image_of_mem _ p₀.1)
  have hx : heldHigh r X W m (d.faceZ s):= (Light (d.faceZ s).1 (p₀.2 s).2).shift (y:=(d.faceZ s).1) (by unfold hallBill Sequest; simp)
  let z:= Real.sqrt β; have hv : Etch.river q (d.faceZ s) (starOf B P r X W m D β V) = z • γ:=by
     unfold starOf coupling; rw [inv_inv,map_smul]; refine congrArg (fun b:G.Color=> z • b) ?_; rw [show γ=Etch.river q (d.faceZ s) (tiler B P (V+D)) from (Etch.river_now ..).symm]; ext i; rw [map_add (tiler B P)]; unfold Etch.river Etch.cup; simp [accessHigh,hx]
  change |_ - skewSig _ _ _ * (Etch.river q (d.faceZ s) (starOf B P r X W m D β V)) d.i|≤ _; rw [raw,reflects,hv]; let r':= skewSig G d.axis s
  change |z*(r'*g d.i)-r'*(z*γ d.i)| ≤ _; rw [show z*_ - _=z*(r'*( (g-γ) d.i)) by change z*(r'*g d.i)-r'*(z*γ d.i)=z*(r'* (g d.i- γ d.i)); ring,abs_mul, abs_of_nonneg (Real.sqrt_nonneg _ |>.trans le_rfl), abs_mul,show |r'|=1 from skewSq ..,one_mul]; apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _) -- tune
  rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le (g-γ) _).trans (grantSlot h u t e (he.1.shift (by simp only [separation_self,zero_add]; unfold hallBill Sequest; omega)) (p₀.2 s).1)
lemma bank_θ : d.spinner q (tiler B P (bank s 0 X))=d.θSlot q s (tiler B P X):=by unfold spinner θSlot; rw [Etch.river_now, Etch.river_now,reflex]; rfl
end Tick
include L in
lemma banks_C (O:Bid.Sworn H n G)(F E:Altar G n→ℂ)(a:Continuous F)(b:Continuous E)(h:∀ V: Dir G n,F (tiler B P (bank s 0 V))= E (tiler B P V)):
 collectionS B P F=collectionS B P E:=by
 let S:= stamen B P n; let M:=stdGaussian (Altar G n)
 have he(Z:Altar G n→ℂ)(w: Continuous Z): collectionS B P Z= ∫ x:S, Z x.val ∂stdGaussian S:=by
    unfold collectionS; simp_rw [← Submodule.coe_orthogonalProjectionOnto_apply]; exact ((integral_map (Regis.curt S).aemeasurable (f:= fun x:S=> Z x.val) (w.comp continuous_subtype_val|>.aestronglyMeasurable)).symm.trans (by rw [(Regis.curt S).map_eq]))
 rw [he F a, he E b]; obtain ⟨i,p⟩:= banked s (0:Site n) B P L O
 have hx(x:S): E x.val= F (i x).val:=by obtain ⟨j,rfl⟩:= (tiler B P).surjective_rangeRestrict x; rw [p]; exact (h j).symm
 conv_rhs=> arg 2; intro i; rw [hx];
 have he:= integral_map (μ:=stdGaussian S) i.continuous.aemeasurable (f:= fun x:S=> F x.val) (a.comp continuous_subtype_val|>.aestronglyMeasurable)
 rw [stdGaussian_map i] at he; exact he
end YM.Gleam.Guide
end
