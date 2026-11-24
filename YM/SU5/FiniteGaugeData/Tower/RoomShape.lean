import YM.SU5.FiniteGaugeData.Tower.Roomer
/-!
# Anisotropic train shape arithmetic

Pay exact clearances on observing lattice. Integer variables v,w code in
double-tick = 16B gauge pitch. Need enough endpoint clearance to compare
on BOTH ends at an almost-half-period stop. Preserve narrow transverse box
round all turns. No assumption on temporal width in the last price.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
variable (K:Calibration)(j:Axis)
local notation "U" i:max=> relocate K j i
local notation "R" i:max=> mirror K j i
local notation "b₀"=>ruler K.B
local notation "r₀" i:max=>gaugeT K i
local notation "J"=> lace K j
local notation "I"=>toward K j
local notation "O"=> plow K j
local notation "f₂" v:max n:max=>b₀ * (v*n)
variable {f x:Family K}{v:ℤ}
lemma pair_between{x y}{u v:ℤ}{S T:Finset Cover}(h:Between K j u v S)(g:Between K j x y T)(p:u ≤ x)(t:v ≤ y): Between K j u y (S∪T):=by
 intro i hi; rcases Finset.mem_union.mp hi with a|a
 · obtain ⟨l,r⟩:=h i a; exact ⟨l,r.trans t⟩
 obtain ⟨l,r⟩:=g i a; exact ⟨(by
                                linarith),r⟩
lemma trans_union {S T:Finset Cover}{X:Axis→ℤ}{d:ℕ}(h:Transom j S X d)(g:Transom j T X d):Transom j (S∪T) X d:=by intro a v i iH; exact (mem_union.mp iH).elim (fun s=>h a v i s) (fun t=>g a v i t)
lemma orient_room {S:Finset Cover}{X d} (p:InTest K true S false f)(t:Between K j 0 (b₀*v) S)(h:Transom j S X d)(n:ℕ): ∃ s:Finset Cover, InTest K true s false (I v f n)∧Between K j 0 (b₀*v) s ∧ Transom j s X d:= by
 induction n with
 | zero=> exact ⟨S,p,t,h⟩
 | succ n ih=>
    obtain ⟨s,p,t,h⟩:=ih; let S':=reflectedBox j (r₀ v) s
    have H:= t.mirror K j (r₀ v); rw [ruler_offset K v,sub_self,sub_zero] at H
    exact ⟨S',axial K j (r₀ v) p,H,h.mirro j _⟩

lemma spans_room {S X₀:Finset Cover}{X:Axis→ℤ}{d:ℕ}{Z:ℤ}(hv:0≤ v)(he:0≤Z) (p:InTest K true S false f)(t:Between K j 0 (b₀*v) S)(h:Transom j S X d)
 (q:InTest K true X₀ false x)(u:Between K j 0 Z X₀)(g:Transom j X₀ X d)(n:ℕ):
 ∃ s:Finset Cover, InTest K true s false (J v f x n)∧Between K j 0 (f₂ v n+Z) s∧Transom j s X d:=by
 induction n with
 | zero=> simpa using (show ∃ s:Finset Cover, InTest K true s false (J v f x 0) ∧ Between K j 0 Z s ∧ Transom j s X d from ⟨X₀,q,u,g⟩)
 | succ n ih=>
    obtain ⟨P,a,b,y⟩:=orient_room K j p t h n
    obtain ⟨U',q,u,g⟩:=ih
    let W:=O v U'
    have hi:InTest K true W false ((U v) (J v f x n)):= flow_port K j _ q; have hx:=g.moved K j v; have ht:=u.relocate K j v
    refine ⟨P∪W, (a.mono subset_union_left).mul (hi.mono subset_union_right),?_,trans_union j y hx⟩
    rw [Nat.cast_add_one,show b₀*(v*(↑n+1))+Z=b₀*v+(f₂ v n+Z) from by ring]
    exact pair_between K j b ht (by rw [add_zero]; exact mul_nonneg (ruler_gene _).le hv) (le_add_of_nonneg_right (by have hg:=ruler_gene K.B; positivity))

lemma trans_exists (m:Finset Cover):∃ X:Axis→ℤ,∃d:ℕ, CompactArc m d ∧ Transom j m X d:=by obtain ⟨d,c⟩:=Tower.sizes m; unfold CompactArc at c; choose X p using c; exact ⟨X,d,fun i=>⟨X i,p i⟩,fun i _=>p i⟩
-- common transverse option
lemma transversePair (S T:Finset Cover):∃ X:Axis→ℤ,∃d:ℕ,Transom j S X d ∧ Transom j T X d:=by obtain ⟨X,d,_,t⟩:=trans_exists j (S∪T); exact ⟨X,d,fun i w v h=>t _ w v (mem_union_left _ h),fun i w v h=>t _ w v (mem_union_right _ h)⟩

lemma spans_only {S X₀:Finset Cover}{Z:ℤ}(hv:0≤ v)(he:0≤Z) (p:InTest K true S false f)(t:Between K j 0 (b₀*v) S) (q:InTest K true X₀ false x)(u:Between K j 0 Z X₀)(n:ℕ):
 ∃ s:Finset Cover, InTest K true s false (J v f x n)∧Between K j 0 (f₂ v n+Z) s:= by
 obtain ⟨w,d,a,b⟩:=transversePair j S X₀
 obtain ⟨s,k,p,_⟩:=spans_room K j hv he p t a q u b n; exact ⟨s,k,p⟩

lemma mainshape {S:Finset Cover}{X d}(hv:0≤v)(p:InTest K true S false f)(t:Between K j 0 (b₀*v) S)(h: Transom j S X d)(n:ℕ):
 ∃ s:Finset Cover, InTest K true s false (J v f 1 n) ∧ Between K j 0 (f₂ v n) s ∧ Transom j s X d:=by
 have hz:Between K j (0:ℤ) (0:ℤ) ∅:=by intro _ h; simp at h
 have he:Transom j ∅ X d:=by intro _ u _ h; simp at h
 simpa using spans_room K j hv (le_refl (0:ℤ)) p t h InTest.one hz he n

-- torus band from cover interval with room both ends; optionally include winding k
lemma enters_arc {x:ℤ}{N:Side}{T:Finset Cover}{c:ℤ} (h:Between K j x (x+N.val) T)(p:x=c): Satin.region T N ⊆ band N j c K.ℓ:=by
 subst c; intro i v; obtain ⟨z,w,rfl⟩:= mem_image.mp v
 obtain ⟨he,hr⟩:= h z w
 rw [band_spec]; change (K.ℓ ≤ ((↑(z j):Per (More N)) - ↑x).val) ∧ _
 change _ ∧ ((↑(z j):Per (More N)) - ↑x).val+K.ℓ≤ N.val
 let k:= z j-x
 have hk:0 ≤ k:=by unfold k; omega
 have hl:k.toNat<(More N).val:=by change _<N.val*2; have hp:0 < N.val:= N.property; unfold k; omega
 rw [←Int.cast_sub, ← Int.toNat_of_nonneg (show 0 ≤ z j-x from hk),Int.cast_natCast,ZMod.val_natCast_of_lt hl]; unfold k at *; omega
-- allow wrapping in moving negative tests directly on refl-presentations when extent crosses both ends; need formula with ∃ y per support
lemma enters_wrapped {N:Side}{S:Finset Cover}{c:ℤ}(h:∀z∈ S,∃ y k:ℤ, y=z j+((2*N.val:ℕ):ℤ)*k∧ c+K.ℓ≤ y∧y+K.ℓ ≤ c+N.val): Satin.region S N ⊆ band N j c K.ℓ:=by
 intro i v; obtain ⟨x,w,rfl⟩:=mem_image.mp v; obtain ⟨y,k,hy,h1,h2⟩:=h x w
 have e:((↑(x j):Per (More N))-↑c)=↑(y-c):=by
    subst y; rw [show 2*N.val=(More N).val by rw [Nat.mul_comm]; rfl]; rw [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast]; simp

 rw [band_spec]; change (K.ℓ ≤ ((↑(x j):Per (More N)) - ↑c).val) ∧ ((↑(x j):Per (More N)) - ↑c).val+K.ℓ≤ N.val
 have hk:0≤y-c:=by omega
 have hl:(y-c).toNat <(More N).val:=by change _ <N.val*2; have ht:0 < N.val:= N.property; omega
 rw [e,← Int.toNat_of_nonneg hk,Int.cast_natCast,ZMod.val_natCast_of_lt hl]; omega
end YM.CF.Buffered.Afterglow.Tower.SlabMark
