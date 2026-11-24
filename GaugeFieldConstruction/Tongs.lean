import YM.SU5.Regis.Easel
import YM.SU5.Circuit.Lark
import GaugeFieldConstruction.Thole
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
variable (s: Signed)(γ:Site n) {K:Support n}{W D':Flaws n}{E:T.Slice G}
-- Fare
lemma hub_okA (Light:LightM r W D' m (signX K s γ))(pW: W=misdemean t U)(hp:FleetS t U) : pingS t K (pull s γ U):=by
 have h:FleetS t (pull s γ U):= by intro f h; exact hp (Face.send s γ f) ((Face.send_price U f s γ _ G.chord_inv (fun i j=> G.chord_conj j i)).symm.trans h)
 apply (shoreK _ _ h _).1; apply disjoint_left.mpr; intro j tL x; let u:= affine s γ j; have hv:u∈ flags t U:= by rw [← Work.H03.flags_send s γ]; exact mem_image_of_mem _ x -- tune
 obtain ⟨i,g,h⟩:= (flags_spec ..).mp hv; let z:= separation u i.1; have hz:z ≤ 2:=by unfold z; rw [separation_comm]; exact Work.E01.sep_touched i _ g
 have hx:hallBill m<z:= (Light u (mem_image_of_mem _ tL)).2 _ (by rw [pW]; exact mem_filter.mpr ⟨mem_univ _,h⟩)
 unfold hallBill Sequest at hx; omega
private lemma endsMA (r:Ratio c n)(x:Step)(a:Site n)(j:Site c)(p:r.parent a=j)(q:r.parent (a+x.vec)=j): InHouse r j (x.used a):=by obtain ⟨i,j'|j'⟩:=x; exact ⟨p,q⟩; exact ⟨(by simpa [Step.used,Step.vec,sub_eq_add_neg] using q),(by simp [Step.used,p])⟩
lemma fare_WA (Light:LightM r W D' m (signX K s γ))(h:TrustLogs X U r (grid_break r D') v) (e: Bond n)(p:e.1∈ K): G.chord ((pull s γ U) e) ≤ v:=by
 let i:= affine s γ e.1; let c:= r.parent i; let b:Step:= (posDir e.2).rotate s; have hg: InHouse r c (b.used i):= endsMA r b i c rfl ((Light i (mem_image_of_mem _ p)).1.2 _ (by
    have hp:separation i (i+b.vec) ≤1:= by unfold b; rw [Step.vec_rotate,Step.vec_pos, show i+_ = affine s γ (e.1+step e.2) from (by unfold i; simp [affine]; abel)]; unfold i affine; rw [show separation (s.act _ + γ) (s.act _ + γ)=separation (s.act e.1) (s.act (e.1+step e.2)) from (by unfold separation; rw [add_sub_add_right_eq_sub]),separation_signed]; exact step_towards e.1 e.2
    unfold hallBill Sequest; omega))
 have hf:G.chord (U (b.used i)) ≤ v:= (h _ ⟨hg.1.symm ▸ (Light i (mem_image_of_mem _ p)).1.1,hg.1 ▸ hg⟩).2
 change G.chord (b.read _ i) ≤ v; unfold Step.read; split_ifs; · rw [G.chord_inv]; exact hf
 exact hf

namespace Tick
variable(d:Tick n G)
abbrev faceZA (s:Signed)(γ:Site n):Cell n:= slotFace (skewSlot G d.axis s) (affine s γ d.o)

private lemma winter (h:d.Compass K f) : (d.faceZA s γ).1∈ signX K s γ:=by
 obtain ⟨p,g,hp⟩:= mem_image.mp (h.2 s).2
 refine mem_image.mpr ⟨p,g,?_⟩
 unfold affine; suffices z: (d.faceZ s).1+γ=(d.faceZA s γ).1 by
   rw [←z,←hp]; simp [affine]
 unfold faceZ faceZA slotFace affine; simp; try abel
lemma raw_costA (p₀: d.Compass K f) (p':W=misdemean t U)(Light:LightM r W D' m (signX K s γ)): |d.raw (pull s γ U)| ≤ t:=by
 let a:=d.axis; let g:=d.o; let b:=d.faceZA s γ
 have ht:d.raw (pull s γ U)=skewSig G d.axis s*((skewSlot G d.axis s).atSite U (affine s γ d.o)) d.i:=by rw [raw,reflects]; rfl
 rw [ht,abs_mul,skewSq,one_mul]; let F:= (skewSlot G d.axis s).atSite U (affine s γ d.o)
 have hy:Brisk r (grid_break r D') W (hallBill m) b.1:= Light b.1 (winter s γ d p₀)
 apply (show |F d.i| ≤ ‖F‖ from by rw [←Real.norm_eq_abs]; exact PiLp.norm_apply_le F _).trans; unfold F; rw [atSite_path, Gauge.norm_adjoint]; apply (G.curvature_norm _).trans; apply le_of_not_gt; intro l
 have h:b∈ W:=by rw [p']; exact mem_filter.mpr ⟨mem_univ _,l⟩; -- tune
 have hp:= hy.2 b h; simp at hp
abbrev θSlotA (q:Clip)(s:Signed)(γ:Site n) : Altar G n→ ℝ:=fun x=> skewSig G d.axis s * (Etch.river q (d.faceZA s γ) x) d.i
abbrev leadSA (q:Clip)(s:Signed)(γ:Site n) : StrongDual ℝ (Altar G n):= (skewSig G d.axis s) • riverOne q (d.faceZA s γ) d.i
lemma leaderA (p:d.Compass K f)(x:Altar G n): |d.leadSA q s γ x|≤ (Real.sqrt q.direct)⁻¹ * bayColour (signX K s γ) x:=by
 change |skewSig _ _ _ * (riverOne q (d.faceZA s γ) d.i x)| ≤ _; rw [abs_mul,skewSq,one_mul]; exact river_serve _ _ _ (winter s γ d p) _
lemma lead_θA (x:Altar G n) : d.leadSA q s γ x=d.θSlotA q s γ x:= rfl
lemma paysA : ‖d.leadSA q s γ‖≤(Real.sqrt q.direct)⁻¹:=by rw [leadSA,norm_smul,Real.norm_eq_abs,skewSq,one_mul]; apply river_norm
lemma angle_SA (Light:LightM r W D' m (signX K s γ))(p₀:d.Compass K f)(h:TrustLogs (V+D) U r (grid_break r D') v)(u:0≤ v)(t:v≤R.c)(p:f≤ m):
  |Real.sqrt β * d.raw (pull s γ U)-d.θSlotA q s γ (starOf B P r (grid_break r D') W m D β V)| ≤ Real.sqrt β * slotError R f v:=by
  let i:= affine s γ d.o; let e:= skewSlot G d.axis s; let X:= grid_break r D'; let g:=e.atSite U i; let Gμ:=faceCurl (slotFace e i) (V+D)
  have he: Brisk r X W (hallBill m) i:= Light i (mem_image_of_mem _ p₀.1)
  have hx : heldHigh r X W m (d.faceZA s γ):= (Light (d.faceZA s γ).1 (winter s γ d p₀)).shift (y:=(d.faceZA s γ).1) (by unfold hallBill Sequest; simp)
  let z:= Real.sqrt β; have hv : Etch.river q (d.faceZA s γ) (starOf B P r X W m D β V) = z • Gμ:=by
     unfold starOf coupling; rw [inv_inv,map_smul]; refine congrArg (fun b:G.Color=> z • b) ?_; rw [show Gμ=Etch.river q (d.faceZA s γ) (tiler B P (V+D)) from (Etch.river_now ..).symm]; ext i; rw [map_add (tiler B P)]; unfold Etch.river Etch.cup; simp [accessHigh,hx]
  change |_ - skewSig _ _ _ * (Etch.river q (d.faceZA s γ) (starOf B P r X W m D β V)) d.i|≤ _; rw [raw,reflects,hv]; let r':= skewSig G d.axis s
  change |z*(r'*g d.i)-r'*(z*Gμ d.i)| ≤ _; rw [show z*_ - _=z*(r'*( (g-Gμ) d.i)) by change z*(r'*g d.i)-r'*(z*Gμ d.i)=z*(r'* (g d.i- Gμ d.i)); ring,abs_mul, abs_of_nonneg (Real.sqrt_nonneg _ |>.trans le_rfl), abs_mul,show |r'|=1 from skewSq ..,one_mul]; apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _) -- tune
  rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le (g-Gμ) _).trans (grantSlot h u t e (he.1.shift (by simp only [separation_self,zero_add]; unfold hallBill Sequest; omega)) (p₀.2 s).1)
lemma bank_θA : d.spinner q (tiler B P (bank s γ X))=d.θSlotA q s γ (tiler B P X):=by unfold spinner θSlotA; rw [Etch.river_now, Etch.river_now,reflex]; rfl
end Tick
include L in
lemma banks_CA (O:Bid.Sworn H n G)(F E:Altar G n→ℂ)(a:Continuous F)(b:Continuous E)(h:∀ V: Dir G n,F (tiler B P (bank s γ V))= E (tiler B P V)):
 collectionS B P F=collectionS B P E:=by
 let S:= stamen B P n; let M:=stdGaussian (Altar G n)
 have he(Z:Altar G n→ℂ)(w: Continuous Z): collectionS B P Z= ∫ x:S, Z x.val ∂stdGaussian S:=by
    unfold collectionS; simp_rw [← Submodule.coe_orthogonalProjectionOnto_apply]; exact ((integral_map (Regis.curt S).aemeasurable (f:= fun x:S=> Z x.val) (w.comp continuous_subtype_val|>.aestronglyMeasurable)).symm.trans (by rw [(Regis.curt S).map_eq]))
 rw [he F a, he E b]; obtain ⟨i,p⟩:= banked s γ B P L O
 have hx(x:S): E x.val= F (i x).val:=by obtain ⟨j,rfl⟩:= (tiler B P).surjective_rangeRestrict x; rw [p]; exact (h j).symm
 conv_rhs=> arg 2; intro i; rw [hx];
 have he:= integral_map (μ:=stdGaussian S) i.continuous.aemeasurable (f:= fun x:S=> F x.val) (a.comp continuous_subtype_val|>.aestronglyMeasurable)
 rw [stdGaussian_map i] at he; exact he
end YM.Gleam.Guide
end
