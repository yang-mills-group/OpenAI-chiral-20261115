import YM.SU5.FiniteGaugeData.Signal.Parlour
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
local notation "N"=> K.c m
-- scalar ONLY
structure Soft (T:Finset Cover)(f:LinksC→ℂ):Prop where
 env:Envelope f
 localV : LocalOn T f
lemma press {T:Finset Cover}{f:LinksC→ℂ}(p:Soft T f): Coeff true T (f∘Prod.fst):= ⟨fun x=>by contradiction,Push.SectorMeasure.Env.along p.env measurable_fst,fun x y t h=> p.localV x.1 y.1 t ⟩

def stucco(f:LinksC→ℂ) : Γ := scalar K (f∘Prod.fst)
lemma stucco_mem {T:Finset Cover}{f:LinksC→ℂ}(p:Soft T f): InTest K true T false (stucco K f):= InTest.seed (press p)
-- terms submodule
abbrev work (f:Γ) := InTest K true T false f

def Flying := Submodule.span ℂ { i:Buffered.Family K| ∃ f : LinksC→ℂ, Soft T f ∧ ∃ v∈price K l S L,i=(stucco K f)*v}

variable (p:∀ i∈S,nodeC i∈T)(e:∀ i∈L,nodeC i∈T)
include p e
lemma secure {f:Γ}(h:f∈Flying K l S T L):
    InTest K true T false f ∧ (∀ m:Side,∀ x a b, f m (x,a)=f m (x,b)) ∧ ∀ m:Side,∀ x, f m x∈ generous l (S.image (wrap (K.c m))) (L.map (wrap (K.c m))) := by
 induction h using Submodule.span_induction with
 | mem x h=>
    obtain ⟨f,t,y,h,rfl⟩:= h; have hp:= stern K l S T L p e h; change InTest _ _ _ _ _ ∧_ at hp; refine ⟨InTest.mul (stucco_mem K t) hp.1,fun m x a b=> congrArg (fun z:FC (Single (K.c m))=> stucco K f m (x,a)*z) (hp.2 m (x,a) (x,b)),fun m x=>?_⟩
    change (f _ • (1:FC (Single (K.c m)))) * y m x ∈ _; rw [Algebra.smul_mul_assoc,one_mul,←price_result K l m S L x]; exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem h)
 | zero=> exact ⟨InTest.zero,fun _ _ _ _=>rfl,fun _ _=>Submodule.zero_mem _⟩
 | smul c x t v=> exact ⟨v.1.smul c,fun m x' a b=> congrArg (fun z:FC (Single (K.c m))=> c • z) (v.2.1 m x' a b),fun m x=>Submodule.smul_mem _ _ (v.2.2 m x)⟩
 | add x y h t u w=> exact ⟨u.1.add w.1,fun m x a b=>congrArg₂ (·+·) (u.2.1 m x a b) (w.2.1 m x a b),fun m x'=>Submodule.add_mem _ (u.2.2 m x') (w.2.2 m x')⟩

-- onscreen boarding at one PERIOD even though Flying is enormous Family-valued.
variable (G:Window.Evaluation (K.c m))(h:RG.Envelope G)(p0:LocalOn (region T (K.c m)) G)
variable (t: Hosp (tips T) (K.c m)) (W:∀ x,G x∈ generous l (S.image (wrap (K.c m))) (L.map (wrap (K.c m))))
local notation "V"=> generous l (S.image (wrap (K.c m))) (L.map (wrap (K.c m)))
include h p p0 t W
lemma shutter : ∃ f∈ Flying K l S T L,∀ x,f m x=G x.1:=by
 let L' := generous l (S.image (wrap (K.c m))) (L.map (wrap (K.c m))); let f(x):L':=⟨G x,W x⟩; let B:= Module.finBasis ℂ L'; let α:= Fin (Module.finrank ℂ L'); let F(i:α): Pane N → ℂ:=(B.coord i) ∘ f
 have hM:Measurable f:= by
    exact h.meas.subtype_mk
 have ht(i:α): Envelope (F i):= Girt.pole_w f _ (B.coord i).continuous_of_finiteDimensional ⟨hM,h.cost.choose,fun x=> h.cost.choose_spec x⟩ -- norm induced
 let Q: α→LinksC→ℂ:=fun i=>F i ∘ graft T N; have hp(i:α): Soft T (Q i):= by
    refine ⟨Push.SectorMeasure.Env.along (ht i) (graft_b ..),fun x y p=>?_⟩; unfold Q F; change B.coord i _=B.coord i _; exact congrArg (fun z:L'=> B.coord i z) (Subtype.ext (p0 _ _ (graft_agrees t p)))
 have he(i:α):∃ g∈price K l S L,∀ x, g m x=(B i).val:=by
    have hv: (B i).val∈ Submodule.map ((res0 K m 1).toLinearMap) (price K l S L):= by rw [price_result]; exact (B i).property
    obtain ⟨y,lx,v⟩:= hv; have ht':InTest _ true _ false y∧_:= (stern K l S T L p e lx); exact ⟨y,lx,fun x=> (ht'.2 m x 1).trans v⟩ -- l shadow
 choose g z l0 using he; let X(i:α):=stucco K (Q i)*g i
 refine ⟨∑ i:α,X i, Submodule.sum_mem _ (fun i _=>Submodule.subset_span ⟨Q i,hp i,g i,z i,rfl⟩),fun x=>?_⟩; have hh(i:α):X i m x= F i x.1 • (B i).val:=by
    have he: Q i (onC N x.1)=F i x.1:=congrArg (fun z:L'=>B.coord i z) (Subtype.ext (p0 _ _ (regrown (roomy t) x.1)))
    change (Q i _ • (1:FC _)) * g i m x = _; rw [Algebra.smul_mul_assoc,one_mul,l0,he]
 simp_rw [Finset.sum_apply,hh]; have hv:=B.sum_repr (f x.1); change _= L'.subtype (f x.1); rw [←hv]; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul]; rfl
end Parfume
end YM.CF.Signal.Scherzo
#print axioms YM.CF.Signal.Scherzo.Parfume.shutter
