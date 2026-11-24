import YM.SU5.FiniteGaugeData.Signal.Breaths
import YM.SU5.FiniteGaugeData.Concord.CoverGauge
/-!
# Carry cover charge for overlapping stencils only. Do not pretend that pulls seeking much
 larger supports at higher levels retain stencil-word shape. Same frame with issue_m.
 ALL physical Wilson junctions (one version) supported in terms of THESE shapes; frame read with
 one pointed removal per site in list (which are supposed to be distinct on cover), and all creators
 at separately charged set on contributing observing s. Pay broad shapes; no assertion of persistence
 when changing observing s. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal.Scherzo
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
variable (K:Calibration)(l:Flavor)(m:Side)(S T:Finset Cover)(L:List Cover)
namespace Parfume
local notation "Γ"=> Buffered.Family K

def input (v:Cover): Submodule ℂ (Buffered.Family K):= Submodule.span ℂ (Buffered.removal K v 2 '' (colors l:Set SU.Slot))

def output: Submodule ℂ (Buffered.Family K):= Submodule.span ℂ {x| ∃ v∈ S,∃ i∈plusHalf,∃ k∈ colors l,x=creation K v i k}
def ships (x:Cover):= input K l x* output K l S
def price := (L.map (ships K l S)).prod

def static (K:Calibration)(T:Finset Cover)(h:Bool):Submodule ℂ (Buffered.Family K) where
 carrier:={f| InTest K true T h f ∧ ∀ (n:Side) x y,f n x=f n y}
 zero_mem':= ⟨InTest.zero,fun _ _ _=>rfl⟩
 smul_mem':=fun c x (p:InTest K true T h x∧_)=>⟨p.1.smul c,fun n k v=>congrArg (fun x: FC (Single (K.c n))=> c • x) (p.2 n k v)⟩
 add_mem':=fun {x y} (p:InTest K true T h x∧_) (q:InTest K true T h y∧_)=>⟨p.1.add q.1,fun n k v=>congrArg₂ (·+·) (p.2 n k v) (q.2 n k v)⟩
lemma static_mul {a b:Bool} : static K T a*static K T b ≤ static K T (a.xor b):=Submodule.mul_le.mpr fun f hf g hg=> by change InTest _ _ _ _ f∧_ at hf; change InTest _ _ _ _ g ∧_ at hg; exact ⟨hf.1.mul hg.1,fun i y z=>congrArg₂ (·*·) (hf.2 i y z) (hg.2 i y z)⟩
lemma inputL (x:Cover)(p:nodeC x∈T): input K l x ≤ static K T true:= Submodule.span_le.mpr (by rintro _ ⟨i,l,rfl⟩; exact ⟨InTest.remover _ (by decide) p,fun i x y=>rfl⟩)
lemma outputL (p:∀ i∈S,nodeC i∈T):output K l S ≤ static K T true:= Submodule.span_le.mpr (fun f h=>by obtain ⟨v,l,i,h,k,g,rfl⟩:=h; exact ⟨InTest.creator _ h (p v l),fun i x y=>rfl⟩)
lemma ship_static (p:∀ i∈S,nodeC i∈T)(x:Cover)(e:nodeC x∈T): ships K l S x ≤ static K T false:= le_trans (b:=static K T true*static K T true) (mul_le_mul' (inputL K l T _ e) (outputL K l S T p)) (static_mul ..)
lemma stern (p:∀ i∈S,nodeC i∈T)(e:∀ i∈L,nodeC i∈T): price K l S L≤ static K T false:=by
 induction L with
 | nil=> exact Submodule.one_le.mpr ⟨InTest.one,fun i x y=>rfl⟩
 | cons i L ih=> exact le_trans (b:=static K T false*static K T false) (mul_le_mul' (ship_static K l S T p i (e _ List.mem_cons_self)) (ih (fun j v=>e j (List.mem_cons_of_mem _ v)))) (static_mul ..)

local notation "N"=> K.c m
variable (V : Fields (K.c m))
def res0 : Buffered.Family K →ₐ[ℂ] FC (Single (K.c m)) where
 toFun x:=x m V
 map_one':= rfl
 map_zero':= rfl
 map_mul' _ _:=rfl
 map_add' _ _:=rfl
 commutes' _:=rfl
local notation "η"=>(res0 K m V).toLinearMap
lemma byte (v:Cover): ‖Lifted.winding N v‖=1:=fee_norm _
lemma arriva_result (v:Cover)(i:SpinIdx)(t:SU.Slot): η (creation K v i t)= Lifted.winding N v • put ((wrap N v,i),t):=by
 change create (basisC _ _ _ _)=_; rw [basisC,map_smul,create_put]; rfl
lemma remova_result (v:Cover)(i:SpinIdx)(t:SU.Slot): η (Buffered.removal K v i t)= star (Lifted.winding N v) • takeF ((wrap N v,i),t):=by
 change Fock.remove (basisC _ _ _ _) = _; rw [basisC, Fock.remove,map_smul,star_smul,create_put]; rfl
lemma input_result (v:Cover) : Submodule.map η (input K l v)=removals l (wrap N v):=by
 apply le_antisymm (Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
 · rintro _ ⟨i,p,rfl⟩; change η _ ∈ removals l (wrap N v); rw [remova_result]; apply Submodule.smul_mem; apply Submodule.subset_span; refine ⟨_,?_,rfl⟩; exact mem_filter.mpr ⟨mem_univ _,mem_singleton_self _,mem_singleton_self _,(mem_filter.mp p).2⟩
 rintro _ ⟨⟨⟨x,i⟩,k⟩,l',rfl⟩; simp [tube] at l'; -- may not reduce cast
 obtain ⟨rfl,rfl,p⟩:= l'; let t:= star (Lifted.winding N v); have hp:t≠0:=star_ne_zero.mpr (norm_pos_iff.mp (by rw [byte K m]; norm_num))
 refine ⟨t⁻¹ • Buffered.removal K v 2 k, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,mem_filter.mpr ⟨mem_univ _,p⟩,rfl⟩),?_⟩
 rw [map_smul,remova_result, inv_smul_smul₀ hp]
lemma output_result : Submodule.map η (output K l S)=arrivals l (S.image (wrap N)):=by
 apply le_antisymm (Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
 · rintro _ ⟨v,k,i,s,b,u,rfl⟩; change η _ ∈ arrivals l (S.image (wrap N)); rw [arriva_result]; apply Submodule.smul_mem; apply Submodule.subset_span; refine ⟨_,?_,rfl⟩; exact mem_filter.mpr ⟨mem_univ _,mem_image_of_mem (wrap N) k,s,(mem_filter.mp u).2⟩
 rintro _ ⟨⟨⟨x,i⟩,k⟩,l',rfl⟩; simp [tube] at l'; obtain ⟨⟨x,b,rfl⟩,p,h⟩:= l'; let t:= Lifted.winding N x; have hp:t≠0:=norm_pos_iff.mp (by unfold t; rw [byte K m]; norm_num)
 refine ⟨t⁻¹ • Buffered.creation K x i k,Submodule.smul_mem _ _ (Submodule.subset_span ⟨x,b,i,p,k,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩),?_⟩
 rw [map_smul,arriva_result, inv_smul_smul₀ hp]

lemma price_result : Submodule.map η (price K l S L)= generous l (S.image (wrap N)) (L.map (wrap N)):=by
 induction L with
 | nil=> change Submodule.map η 1=1; exact Submodule.map_one _ -- tune
 | cons i L ih=> simp only [price, generous,List.map_cons, List.prod_cons, Submodule.map_mul, ships,books]; simp only [Submodule.map_mul,input_result,output_result]; exact congr_arg (_ * ·) ih
end Parfume
end YM.CF.Signal.Scherzo
