import YM.SU5.Selected.Prag.Sol
import YM.SU5.Selected.Actress.Altar
import YM.SU5.Selected.Actress.Scarves
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxHeartbeats 290000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open Function Filter Metric Topology NormedSpace
open scoped BigOperators Kronecker InnerProductSpace ComplexOrder NNReal ENNReal Classical
variable {Γ:AddSubgroup ℝ} {A:Hilbert}{j:Axis}(P:Alliance (Trans j) Γ A) (dp:Dense (Γ:Set ℝ)) (S: OS.Semigroup A j)(q: ∀ i v t, Commute ((P.crew i).play v) (S.E t))
local notation "u" t:max=> S.E t
local notation "L₀"=> P
local notation "δ"=> dp
local notation "X"=> look j
local notation "T₀"=> (L₀).Realm X
local notation "Y"=> prism P
local notation "V"=> Frog P dp S q
open Spectral Spectral.Alps
-- height-free compression. Chron packing based on same labels **without equality of P multiplications**
local notation "U"=> OS.Cross j
local notation "Ζ" x:max=> P.aviator x
local notation "R"=> arise P
local notation "d"=> descendH P
local notation "π"=> P.stackS X
noncomputable def bead (H:A.Op): (T₀).Op:= (d).comp (H.comp R)
local notation "ρ"=> bead P
variable (x y:A)
lemma beadU (p:A.Op)(e: x ∈ P.aviator X): (ρ p) (Y x)= Y (p x):=by
 change d (p (R (Y x)))= _; rw [rebuilt P _ e,descends]
lemma trap(x y:T₀)(c:A.Op):inner ℂ x ((ρ c) y)=inner ℂ (R x) (c (R y)):= (cityH P ..).symm
lemma bead_star(p:A.Op): ρ (star p)=star (ρ p):=by ext1 x; apply ext_inner_left ℂ; intro y; rw [trap P]; symm; change inner ℂ _ ((ρ p).adjoint x)=inner ℂ _ (p.adjoint _); rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm ..).symm.trans ((congrArg (starRingEnd ℂ) (trap P x y p)).trans (inner_conj_symm ..))
lemma bead_space (i:Trans j)(x:Γ)(F' G:A.Op)(p: (P.crew i).play x*F'=G*(P.crew i).play x): (V).U (aSpot i x)*ρ F'=ρ G* (V).U (aSpot i x):=by
 let A':= (V).U (aSpot i x); let B:= (P.crew i).play x; ext1 a; apply Subtype.ext; have he : B.comp π=(π).comp B:= P.ground _ _ (fun r _ c=> P.cCom r i c x); change R (A' ((ρ F') a))= R ((ρ G) (A' a)); have ht:∀ (F:A.Op)(t:T₀), R ((ρ F) t)= π (F (R t)):= fun _ _=> propels P _
 rw [(show R (A' _) =_ from P.spotR dp S q i x _),ht,ht,show R (A' _) =_ from P.spotR dp S q i x _]; exact (DFunLike.congr_fun he _).trans (congrArg π (DFunLike.congr_fun p _)) -- holes
variable {H:Hilbert}{a:Axis}
variable (F:OS.Semigroup H a) (p r:OS.Cross a)
-- unitary action full. `labelSet`.
private lemma Hsum (p r: OS.Cross a): F.U p * F.U r = F.U (p+r):= (F.space ..).symm
private lemma rootS:F.U 0=1:=F.uZero
lemma cope_star :star (F.U p)=F.U (-p):=by
 have he: star (F.U p)* F.U p=1:= (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (F.U p)).1 (F.unitary p); calc
  _= (star (F.U p)* F.U p)*F.U (-p):=by rw [mul_assoc,Hsum,add_neg_cancel,rootS,mul_one]
  _= _:=by rw [he,one_mul]
noncomputable def Arden : unitary H.Op:= ⟨F.U p,⟨by rw [cope_star,Hsum,neg_add_cancel,rootS],by rw [cope_star,Hsum,add_neg_cancel,rootS]⟩⟩
noncomputable def Vista : H.Op≃⋆ₐ[ℂ] H.Op:= Unitary.conjStarAlgAut ℂ H.Op (Arden F p)
lemma contemplate (B':H.Op) : Vista F p B'=F.U p* B' * F.U (-p):=by unfold Vista; rw [Unitary.conjStarAlgAut_apply,show star ((Arden F p:unitary H.Op):H.Op)=F.U (-p) from cope_star F p]; rfl
lemma twoS(B': H.Op): Vista F p (Vista F r B')=Vista F (p+r) B':=by
 unfold Vista; rw [← Unitary.conjStarAlgAut_mul_apply]; exact congrArg (fun Z: unitary H.Op=> Unitary.conjStarAlgAut ℂ H.Op Z B') (Subtype.ext (Hsum F ..))
lemma onVista(B:H.Op): Vista F 0 B=B:=by rw [contemplate,neg_zero,rootS]; simp
lemma swapper(A' B:H.Op)(t: F.U p*A'=B*F.U p) : Vista F p A'= B:=by rw [contemplate,t,mul_assoc,Hsum,add_neg_cancel,rootS,mul_one]
variable {κ:Type}(B:κ→ A.Op)
local notation "S₀"=> P.prism x
-- spatiotemporally strong (doesn't imply norm-continuity). further available. fill Epoch-by. Keep comparison before after.
noncomputable def Arcadia (f:κ × OS.Cross j): (T₀).Op := Vista V f.2 (bead P (B f.1))
local notation "Θ"=> Arcadia P dp S q B
lemma home(i:κ): Θ (i,0)=ρ (B i):= onVista ..
lemma risen (u₀:OS.Cross j)(i: κ × OS.Cross j): Vista (V) u₀ (Θ i)=Θ (i.1,u₀+i.2):= twoS ..
lemma Asphalt: Alps.JMotion (V) (Θ) (Arden V):=by
 intro i; refine ⟨fun t=> Commute.symm ((V).both t i : ((V).edge t).comp ((V).U i)=_),?_⟩; intro t; refine ⟨(t.1,i+t.2),?_⟩; rw [←risen, contemplate]; change (V).U i * _ = _ * (V).U i; rw [mul_assoc ((V).U i * (Θ t)), Hsum,neg_add_cancel,rootS,mul_one]
lemma balconyP (j:Trans j)(x:Γ) (i i':κ)(v:(P.crew j).play x*B i=B i'*(P.crew j).play x): Θ (i,aSpot j x) = Θ (i',0) := by rw [home]; change Vista (V) _ _= _; exact swapper _ _ _ _ (bead_space _ _ _ _ _ _ _ _ v)
local notation "Λ₀"=> Arden (V)
lemma activeDense(p:x∈P.aviator (look j))(t:DenseRange (fun i:κ=> B i x)) : DenseRange (fun i:κ × OS.Cross j=> Θ i (Y x)):=by
 have hd:= (show Function.Surjective ⇑d from fun i=> ⟨_, descends_d P i⟩).denseRange.comp t (d).continuous; exact hd.mono (Set.range_subset_iff.mpr fun i=> ⟨(i,0),by change Θ (i,0) (Y x) = _; rw [home,beadU P _ _ p]; exact (descends P _).symm⟩) -- Lemmas syntax
-- extremality under full Tran & widths. only measures as Urbana. 
theorem stationCity (p:x∈ S.ground)(h: ‖x‖=1)(t:DenseRange (fun i:κ=> B i x))(v:Follows P x)(w:∀ y:A,Follows P y→(∀ i:ℝ,S.edge i y=y)→∃ n:ℂ,n • x=y): Urbana V (Y x) Θ (Λ₀):=by
 exact city V (Y x) Θ Λ₀ (follows_norm P dp S q x v h) (follows_heat _ _ _ _ _ v p) (activeDense _ _ _ _ _ B (follows_mem _ _ v) t) (Asphalt _ _ _ _ B) (fun u₀=> follows_full P dp S q x v u₀) (fun i h=> fellows P dp S q x v w i (fun p=> h (.inr p)) (fun p=> h (.inl p)))
end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
#print axioms stationCity
#print axioms Asphalt
#print axioms balconyP
#print axioms bead_star
#check @beadU
