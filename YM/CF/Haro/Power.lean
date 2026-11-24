import YM.CF.Haro.Ledge
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable{n:Side}(F:Op (Single n))(h:AxisB F)
def porchY(n:Side):Finset Cover:= Finset.univ.image fun i:Site n × Signed=> i.2.act (lift i.1)
def portY(x:Site n):Finset Cover:= (porchY n).filter fun y=>wrap n y=x
def loft(z:Cover):Pal:= if z∈porchY n then ((portY (wrap n z)).card:ℝ)⁻¹ • tapH F z else 0
lemma loft_x(p:Cover)(g:p∈porchY n)(s:Signed): s.act p ∈ porchY n:=by obtain ⟨⟨x,j⟩,h,rfl⟩:= Finset.mem_image.mp g; exact Finset.mem_image.mpr ⟨(x,s*j),mem_univ _, Signed.act_mul ..⟩
lemma loft_g(y:Cover)(s:Signed):s.act y∈ porchY n ↔ y∈porchY n:= ⟨fun h=> by simpa using loft_x _ h s⁻¹,fun h=>loft_x _ h s⟩
lemma port_p (x:Site n): (portY x).Nonempty:=⟨lift x,mem_filter.mpr ⟨mem_image.mpr ⟨(x,1),mem_univ _,by simp⟩,wrap_lift _⟩⟩
lemma pitch_l (x:Site n)(s:Signed): (portY (s.act x)).card=(portY x).card:=by
 rw [show portY (s.act x)= (portY x).image s.act from ?_, card_image_of_injective _ s.act_injective]; ext y; simp only [mem_image]; constructor
 · intro p; obtain ⟨b,rfl⟩:= (s.actEquiv (R:=ℤ)).surjective y; refine ⟨b,?_ ,rfl⟩; obtain ⟨hx,u⟩:= mem_filter.mp p; apply mem_filter.mpr; change wrap _ (s.act b) =_ at u; rw [←wrap_signed] at u; exact ⟨(loft_g b s).mp hx,s.act_injective u⟩
 rintro ⟨b,t,rfl⟩; obtain ⟨v,p⟩:= mem_filter.mp t; exact mem_filter.mpr ⟨loft_x _ v s,by rw [←wrap_signed,p]⟩
abbrev flipL:Signed:= ⟨Equiv.refl _,fun _=>true⟩
lemma flip_p(z:Cover): flipL.act z= -z:=by funext i; simp [Signed.act,flipL]
include h
lemma price_p(x:Cover)(s: Signed)(b:Bool)(U:UNI SpinIdx)(p:JetS s b (detX s) U): sings b (twoU U b) (loft F (s.act x))=if detX s then -star (loft F (-x)) else loft F x:=by
 have hl : -x∈porchY n ↔ x∈porchY n:= flip_p x ▸ loft_g x flipL
 have hm : (portY (wrap n (-x))).card=(portY (wrap n x)).card:=by rw [←flip_p,←wrap_signed,pitch_l]
 unfold loft; by_cases z:x∈ porchY n
 · rw [if_pos z,if_pos ((loft_g x s).mpr z), if_pos (hl.mpr z),singT,win_r,map_smul,←singT, taste_g F h s b U p,←wrap_signed,pitch_l,hm]; cases hx:detX s <;>simp [hm]
 rw [if_neg z,if_neg (mt (loft_g x s).mp z), if_neg (mt hl.mp z)]; simp [singT,win_z]
lemma gift : love n (cart n (loft F))= F :=by
 apply (love n).symm.injective; change (love n).symm ((love n) (cart n (loft F)))=(love n).symm F; rw [StarAlgEquiv.symm_apply_apply]; ext ⟨x,i⟩ ⟨y,j⟩; let d:=y-x; let t:= portY d; let Q(z:Cover):= wagon n (loft F) z (x,i) (y,j)
 change (∑' z,Q z)=_; have hv(z:Cover): z∉ t→Q z=0:=by
    intro p; unfold Q; rw [wagon_app]; split; swap; rfl
    next hx=> have hz:wrap n z=d:= eq_sub_of_add_eq' hx -- tune
              simp [loft,show z ∉ porchY n from fun h=>p (mem_filter.mpr ⟨h,hz⟩)]
 let u:= (love n).symm F; let W:= u (x,i) (y,j); have hz(z)(v:z∈t): Q z=(t.card:ℝ)⁻¹ • W:=by
    obtain ⟨he,g⟩:= mem_filter.mp v; unfold Q; rw [wagon_app,if_pos (show x+wrap _ z=y from by rw [g]; unfold d; abel),loft,if_pos he,g]; rw [Matrix.smul_apply]
    have h:=taff F h x z; rw [show x+wrap _ z=y from by rw [g]; unfold d; abel] at h; rw [show W= Rush.wind x z • tapH F z i j from congrArg (fun w:Pal=>w i j) h]; exact (smul_comm (Rush.wind x z) ((t.card:ℝ)⁻¹) _)
 rw [tsum_eq_sum (s:=t) hv, sum_congr rfl hz,sum_const,show t.card • ((t.card:ℝ)⁻¹ • W)= (t.card:ℝ) • ((t.card:ℝ)⁻¹ • W) from (Nat.cast_smul_eq_nsmul ..).symm,smul_smul,mul_inv_cancel₀ (by exact_mod_cast (card_pos.mpr (port_p d)).ne'),one_smul]
end YM.CF.Haro
