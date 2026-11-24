import YM.SU5.FiniteGaugeData.Lapis.Grove
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LapisS
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.Lapis Lumi Eight
open Next.Rank Spindle Push.Local Rhythm LightK
variable {ι:Type}[Fintype ι][DecidableEq ι]
variable (T:Duct SU.group ι)(K:Clip)(r x α:ℝ){N:Side}
local notation "I₁"=> Lumi.macroK ι T
local notation "P"=> Spindle.patch I₁
local notation "F"=>Mark N
local notation "S"=> Support (More N)
variable {a b:Mark N}{p q:Support (More N)}{j k:ℕ}
structure Packed (T:Duct SU.group ι)(K:Clip)(r x α:ℝ)(j:ℕ)(p:Support (More N))(a:Mark N):Prop where
 store : ∃ (Y:Finset (Site (More N)))(D:Site (More N)→Signed), Y.card=j ∧ Lumi.tribe T Y ∧ (∀ i∈ Y, Spindle.patch (macroK ι T) i ⊆ p) ∧ SoonP (Lumi.makes T K x r D Y) (j*α) a
namespace Packed
variable {T K r x α} (A:Packed T K r x α j p a)
-- Supports enlarge okay.
include A in
lemma expand (u:p⊆q): Packed T K r x α j q a:=by obtain ⟨Y,D,t,v,e,r⟩:=A.store; exact ⟨Y,D,t,v,fun i h=>(e i h).trans u,r⟩ -- potential wrong constructor Exist
lemma singleton_t(x₀:Seat N)(s:Signed)(b:S)(h: Spindle.patch (macroK ι T) x₀ ⊆ b) (e:SoonP (Lumi.makes T K x r (fun _=> s) {x₀}) α a) : Packed T K r x α 1 b a := by
 refine ⟨{x₀},fun _=>s,card_singleton _,?_,fun i e=> by simpa only [mem_singleton.mp e] using h,(by simpa only [Nat.cast_one,one_mul] using e)⟩
 intro y i z f t; exact (t ((mem_singleton.mp i).trans (mem_singleton.mp f).symm)).elim
lemma unit (p:S): Packed T K r x α 0 p 1:= by
 refine ⟨∅,fun _=>1,card_empty,?_,fun x e=>False.elim (notMem_empty _ e),fun i=>⟨1,(one_smul ..).symm,by simp [Lumi.makes]⟩⟩
 intro i v; exact False.elim (notMem_empty _ v)
include A
lemma both (B:Packed T K r x α k q b)(u:Disjoint p q) : Packed T K r x α (j+k) (p∪q) (a*b):=by
 obtain ⟨Y,D,e,z,t,aP⟩:= A.store; obtain ⟨Z,Q,h,hq,w,B₁⟩:= B.store; let D' := fun i:Seat N=>if i∈Y then D i else Q i; let L:Seat N→ S:= Spindle.patch (macroK ι T); have hh(i:Seat N):i∈ L i:=by apply Spindle.doors _ |>.2; rw [separation_self]; omega
 have he(i)(h:i∈ Y)(j)(b:j∈ Z):Disjoint (L i) (L j):= Disjoint.mono (t _ h) (w _ b) u
 have ho:Disjoint Y Z:=Finset.disjoint_left.mpr fun i h b=> Finset.disjoint_left.mp (he i h i b) (hh i) (hh i); refine ⟨Y∪Z,D',by rw [card_union_of_disjoint ho,e,h],?_,?_,?_⟩
 · intro i v j u h; obtain a|a:=Finset.mem_union.mp v; · exact (Finset.mem_union.mp u).elim (fun U=>z a U h) (he i a j)
   exact (Finset.mem_union.mp u).elim (fun h=> (he j h i a).symm) (fun b=>hq a b h)
 · intro i h; exact (Finset.mem_union.mp h).elim (fun i'=> (t i i').trans subset_union_left) (fun i'=> (w i i').trans subset_union_right)
 intro i; obtain ⟨v,a,h⟩:=aP i; obtain ⟨w,b,h₂⟩:=B₁ i; let U:=i.1; refine ⟨v*w,(by rw [Pi.mul_apply,a,b]; simp only [Matrix.mul_smul, mul_one,smul_smul]; rw [_root_.mul_comm w v]),?_⟩; rw [norm_mul]; apply (mul_le_mul h h₂ (norm_nonneg _) (Real.exp_pos _).le).trans_eq; rw [← Real.exp_add]
 have hp(x r:ℝ): Lumi.makes T K x r D' (Y∪Z) U=Lumi.makes T K x r D Y U+Lumi.makes T K x r Q Z U:=by
    unfold Lumi.makes; rw [sum_union ho, mul_add]; apply congrArg₂ (·+·) <;> apply congrArg (x*·)
    · exact sum_congr rfl (fun i v=>congrArg (fun z:Signed=> Lumi.live T K r z i U) (if_pos v)) -- tune
    exact sum_congr rfl (fun i v=> congrArg (fun z:Signed=> Lumi.live T K r z i U) (if_neg (Finset.disjoint_right.mp ho v)))
 change _=Real.exp (Lumi.makes _ _ _ _ _ _ U+_); rw [hp, Nat.cast_add,add_mul]; congr 1; abel

abbrev Fr(s:ℤ)(i:Axis):= (Buffered.plane i s).anon N
lemma turn (z:ℤ)(i:Axis): Packed T K r x α j (p.image ((Buffered.plane i z).anon N)) (reflMark i z a):=by
 obtain ⟨Y,D,e,h,t,r'⟩:=A.store; let s:=Signed.mirror i; let u:= wrap (More N) (2 • (z • step i)); let L:= turnSites s u; have ht: Fr (N:=N) z i=L:=rfl; let W:=posse s u D; refine ⟨Y.image L,W,(card_image_of_injective _ L.injective).trans e,tribe_rot T s u _ h,?_,?_⟩
 · intro x hz; obtain ⟨x,h,rfl⟩:=mem_image.mp hz; rw [show L x=_ from rfl,←Lumi.region_rot s (macroK ι T) u x]; exact image_subset_image (t x h)
 intro y; let U:Fields N:=(fling i z N y.1,fling i z N y.2); obtain ⟨v,b,h⟩:=r' U; refine ⟨star v,?_ ,?_ ⟩
 · change theta _ (a U)=_; rw [b, theta_smul,theta_one] -- tune
 rw [norm_star]; exact (Lumi.ascendant («S»:=Y) T s u D K y.1 (t:=x) (r:=r)) ▸ h -- tune pattern
end Packed
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Packed.both
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Packed.turn
