import YM.SU5.One.Emblem

/-!
# One graded refinement Γ
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry Tapestry.Altitude
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E) (s:ℕ)
variable {D: ℕ→ Family (tent Y H) → Family (tent Y H)}{n m:ℕ→ℕ}(d: Coherent Y H (i:=i) (k:=k) (E:=E) D n m)
local notation "K"=>tent Y H
local notation "𝒮"=> wingspan Λ l

section
variable (M:Collection Λ l)
def stripe (b:Bool)(s:ℕ)(f:Family (tent Y H)):Family (tent Y H):= if h:f∈homTest K b then
 let a:= (show ∃ S, InTest K true S b f from h)
 fresco (𝒮 a.choose) b K (M s a.choose b (kitB _ _ _ a.choose_spec)) else 0

/-- Good resolution with both parity and calibrated mesh - one path.
Keep relation to native operator norm scaling in M.
-/
structure Twined (f:ℕ→ℕ) : Prop where
 thins : StrictMono f
 offers: AdmitsCollection Y H ((i∘n)∘f) ((k∘m)∘f) M
-- corresponds to d by elaboration in later calls, not attached.
end

section pay
variable {M:Collection Λ l}{q:ℕ→ℕ}(τ: Twined Y H (i:=i) (n:=n) (k:=k) (m:=m) M q)
local notation "𝔇"=> stripe Y H M
include d V τ

lemma crucible (b:Bool){f:Family (tent Y H)}{S:Finset Cover}{g:Bazaar S b}(p:f=fresco S b K g):
   stripe Y H M b s f= fresco (𝒮 S) b K (M s S b g):=by
 have ht: InTest K true S b f:= p.symm ▸ plaid S b K g
 let x : ∃ U, InTest K true U b f:=⟨S,ht⟩
 let t:=kitB _ _ _ x.choose_spec
 unfold stripe; rw [dif_pos (show f∈ homTest K b from ⟨S,ht⟩)]
 exact synchronizes Y H V s d τ.offers τ.thins.tendsto_atTop x.choose S b t g ((fresco_kitB ..).trans p)
lemma stripeLocus (b:Bool){f:Family K}{S:Finset Cover}(h:InTest K true S b f): InTest K true (𝒮 S) b (𝔇 b s f):=by rw [crucible Y H V s d τ b (fresco_kitB _ _ _ h).symm]; exact plaid ..
lemma existingD {f:Family K}(p:f∈homTest K false): 𝔇 false s f=D s f:=by
 obtain ⟨S,h⟩:=p; obtain ⟨g,rfl⟩:= outlined S false K h; rw [crucible Y H V s d τ false rfl]; exact tier_cost Y H V s d τ.offers τ.thins.tendsto_atTop S g
lemma stripeScale (b:Bool){f:Family K}(h:f∈homTest K b)(z:ℂ): 𝔇 b s (z • f)=z • 𝔇 b s f:=by
 obtain ⟨S,p⟩:=h; obtain ⟨g,rfl⟩:= outlined _ _ _ p
 rw [crucible Y H V s d τ b rfl,crucible Y H V s d τ b (map_smul (fresco S b K) z g).symm]; rw [map_smul,map_smul]
lemma stripePlus (b:Bool){f g:Family K}(h:f∈homTest K b)(u:g∈homTest K b): 𝔇 b s (f+g)=𝔇 b s f+𝔇 b s g:=by
 obtain ⟨S,p⟩:=h; obtain ⟨T,v⟩:=u
 obtain ⟨k,rfl⟩:= outlined (S∪T) b K (p.mono subset_union_left); obtain ⟨r,rfl⟩:= outlined (S∪T) b K (v.mono subset_union_right)
 rw [crucible Y H V s d τ b (map_add (fresco (S∪T) b K) k r).symm,crucible Y H V s d τ b (g:=k) rfl,crucible Y H V s d τ b (g:=r) rfl,map_add,map_add]
lemma stripeZero (b:Bool): 𝔇 b s 0=0:=by simpa only [zero_smul] using stripeScale Y H V s d τ b (homTest K b).zero_mem 0
lemma stripeTurn (b:Bool){f:Family K}(p:f∈homTest K b) (a:Axis)(z:ℤ): 𝔇 b s (mirror K a z f)=mirror K a ((Λ.R.L.val:ℤ)*z) (𝔇 b s f):=by
 obtain ⟨S,w⟩:=p; let u:=axial K a z w; let l:=fresco_kitB S b K w; let r:= fresco_kitB (reflectedBox a z S) b K u
 rw [crucible Y H V s d τ b r.symm,crucible Y H V s d τ b l.symm]; exact silhouette Y H V s d τ.offers τ.thins.tendsto_atTop S b (kitB S b K w) _ _ a z (by rw [l,r])
lemma stripeSlide (b:Bool){f:Family K}(p:f∈homTest K b) (a:Axis)(z:ℤ): 𝔇 b s (chime K a z f)=chime K a ((Λ.R.L.val:ℤ)*z) (𝔇 b s f):= by
 unfold chime; rw [stripeTurn Y H V s d τ b (homMirror p),stripeTurn Y H V s d τ b p,mul_zero]
lemma stripeH (b:Bool)(P:Cover→ SU.E){f g:Family K}{S:Finset Cover}(p:InTest K true S b f)(t:InTest K true S b g)(e:Circular S (parentGauge Λ P) f g): Circular (𝒮 S) P (𝔇 b s f) (𝔇 b s g):=by
 obtain ⟨a,rfl⟩:= outlined S b K p; obtain ⟨x,rfl⟩:= outlined S b K t; rw [crucible Y H V s d τ b (g:=a) rfl,crucible Y H V s d τ b (g:=x) rfl]; exact charges_survive Y H V s d τ.offers τ.thins.tendsto_atTop S b a x P e
lemma stripeMult {b e:Bool}{S T:Finset Cover}{f g:Family K}(w:InTest K true S b f)(u:InTest K true T e g)(p:Tower.separated (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)) S T) : 𝔇 (b.xor e) s (f*g)=𝔇 b s f*𝔇 e s g:=by
 obtain ⟨a,rfl⟩:=outlined S b K w; obtain ⟨g,rfl⟩:=outlined T e K u
 let Q:=fresco_kitB (S∪T) _ K ((w.mono subset_union_left).mul (u.mono subset_union_right))
 rw [crucible Y H V s d τ (b.xor e) Q.symm, crucible Y H V s d τ b (g:=a) rfl,crucible Y H V s d τ e (g:=g) rfl]; apply enamored Y H V s d τ.offers τ.thins.tendsto_atTop S T b e a g (S∪T) _ Q
 apply farEnough Y H S T s _
 apply Finset.disjoint_left.mpr; intro i h v
 obtain ⟨x,q,h⟩:=mem_biUnion.mp h; obtain ⟨j,t,rfl⟩:=mem_image.mp h
 exact separated_symm p _ v _ q (by rw [add_sub_cancel_right]; exact t)

-- rank-preserving lifts through all levels
abbrev beamB (X : Collection Λ l)(b:Bool):= stream Y H (stripe Y H X b)
local notation "ℒ"=> beamB Y H M
lemma preservesStamp {b:Bool}{F:Family K}{S:Finset Cover}(p:InTest K true S b F) (t:ℕ): InTest K true (volumeAround Λ l t S) b (ℒ b s t F):=by
 induction t with
 | zero=> exact p
 | succ t ih=> exact stripeLocus Y H V (s+t) d τ b ih
lemma stamp_cost {b:Bool}{F:Family K}(p:F∈homTest K b) (t:ℕ): (ℒ b s t F)∈homTest K b:=by obtain ⟨S,h⟩:=p; exact ⟨_,preservesStamp Y H V s d τ h t⟩
lemma carriesPhase {F:Family K}(w:F∈homTest K false) (t:ℕ): ℒ false s t F=stream Y H D s t F:=by
 obtain ⟨S,x⟩:=w; induction t with
 | zero=>rfl
 | succ t ih=> change 𝔇 false (s+t) (ℒ false s t F)=D (s+t) (stream Y H D s t F); rw [ih]; exact existingD Y H V (s+t) d τ ⟨_,(proceeds Y H d.circuit s t x).1⟩
lemma beamAdd {F G:Family K}{b:Bool}(x:F∈homTest K b)(u:G∈homTest K b)(t:ℕ): ℒ b s t (F+G)=ℒ b s t F+ℒ b s t G:=by
 induction t with
 | zero=>rfl
 | succ t ih=> change 𝔇 b (s+t) (ℒ b s t (F+G))=𝔇 b (s+t) _+𝔇 b (s+t) _; rw [show ℒ b s t (F+G)=_ from ih]; exact stripePlus Y H V _ d τ b (stamp_cost Y H V s d τ x t) (stamp_cost Y H V s d τ u t)
lemma beamScale {F:Family K}{b:Bool}(u:F∈homTest K b)(v:ℂ)(t:ℕ): ℒ b s t (v • F)=v • ℒ b s t F:=by
 induction t with
 | zero=>rfl
 | succ t ih=> change 𝔇 b (s+t) (ℒ b s t (v • F))=v • 𝔇 b (s+t) _; rw [show ℒ b s t (v • F)=_ from ih]; exact stripeScale Y H V _ d τ b (stamp_cost Y H V s d τ u t) v
lemma beamTurns {b:Bool}{F:Family K}(p:F∈homTest K b)(i:Axis)(y:ℤ)(t:ℕ): ℒ b s t (mirror K i y F) = mirror K i ((Λ.R.L.val:ℤ)^t*y) (ℒ b s t F):=by
 induction t with
 | zero=>simp only [beamB,stream,pow_zero,one_mul,Nat.rec_zero]
 | succ t ih=> rw [pow_succ',mul_assoc]; change 𝔇 b (s+t) (ℒ b s t (mirror K i y F))=mirror _ _ _ (𝔇 b (s+t) _); rw [show ℒ b s t (mirror K i y F)=_ from ih]; exact stripeTurn Y H V _ d τ b (stamp_cost Y H V s d τ p t) _ _
lemma beamMult {b e:Bool}{F G:Family K}{S T:Finset Cover}(p:InTest K true S b F)(h:InTest K true T e G)(u:Detached Λ l S T)(t:ℕ): ℒ (b.xor e) s t (F*G)=ℒ b s t F * ℒ e s t G:=by
 induction t with
 | zero=> rfl
 | succ t ih=> change 𝔇 _ (s+t) (ℒ (b.xor e) s t (F*G))=𝔇 b (s+t) _ * 𝔇 e (s+t) _; rw [show ℒ (b.xor e) s t (F*G)=_ from ih]; exact stripeMult Y H V _ d τ (preservesStamp Y H V s d τ p t) (preservesStamp Y H V s d τ h t) ((Around_detaches Λ l u t).act Λ l)
lemma beamWing {a:Axis}{z:ℤ}{b:Bool}{F:Family K}(x:F∈gradeFlank K b a z)(t:ℕ): ℒ b s t F∈gradeFlank K b a ((Λ.R.L.val:ℤ)^t*z):=by
 induction t with
 | zero=>simpa only [beamB,stream,pow_zero,one_mul,Nat.rec_zero] using x
 | succ t ih=>
    obtain ⟨S,p,u⟩:=ih; rw [pow_succ',mul_assoc]; exact ⟨_,stripeLocus Y H V (s+t) d τ b p,wingspan_region Y H S a _ u⟩
end pay
end YM.CF.Buffered.Afterglow.Tower.One
