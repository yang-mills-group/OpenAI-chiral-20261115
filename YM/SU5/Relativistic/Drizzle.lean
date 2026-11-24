import YM.SU5.Relativistic.Axact
import YM.SU5.Relativistic.Pernil
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
local notation "W₀" s:max=> Tower.Field Y H s j 0 false
local notation "Ωe"=> doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ" s:max=> arriving Y H V s Q G.clipped j false (c j) (χ j)
local notation "Υ" s:max=> (U).entry s
local notation "E₁"=> indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "E₂"=> (U).booth
local notation "Δ₀"=> relocate (tent Y H)
local notation "B₀"=> ruler Λ.block
open Germ SelectionAnalysis CF.Pannier.Chancel.ScreeV
local notation "vt" s:max=> land Y H V s Q G.clipped j false (c j) (χ j)
local notation "Ωb"=> vocation Y H V Q G.clipped j false (c j) (χ j)
-- genuine selected even history. Needs just nonperturbed seen X.
variable {S T':Finset Cover}{F H':Family (tent Y H)}{z:ℤ}{r:ℕ}(sP:S.Nonempty)(tP:T'.Nonempty)(h:0<r)
local notation "Ξ₀" k:max v:max=> FundX Y H D G d k c x s (T:=T) S T' F H' v
local notation "dyn" k:max=> Soft Y H D G (T:=T) d k c x s
structure Actually (F H':Family (tent Y H)) (S T':Finset Cover)(z:ℤ)(r:ℕ) :Prop where
 focal : FundX Y H D G d j c x s (T:=T) S T' F H' false z r
 portal : ∃ (A B':Tower.Field Y H s j 0 false),Curated Y H D G (T:=T) d j c x s F H' z A B'∧
    inner ℂ ((vt s) A) ((vt s) B')≠ inner ℂ ((vt s) A) Ωb * inner ℂ Ωb ((vt s) B') ∧
    ∀ p:ℂ,(vt s) A ≠ p • Ωb ∧ (vt s) B' ≠ p • Ωb
include t
lemma inaugurate (v:(Ξ₀ j false) z r)(w:∀ k:Axis,(dyn k) false F H'): Actually Y H D G (T:=T) d j c x s F H' S T' z r:=by
 obtain ⟨A,B',q⟩:= maven_act Y H D G u t d j c x s v.input.widen v.certified.widen v.gap (fun i=> w i.val)
 have p:= maven_gain Y H D G u t d j c x s q v.input.widen v.certified.widen
 have hv: ψ s (F*H') ≠ ψ s F*ψ s H':=by
    obtain ⟨r₁,g,u⟩:=v.nonfactorCoordinate; specialize u 0
    change r₁≤ ‖ψ s (F*H')-ψ s F*ψ s H'‖ at u; exact sub_ne_zero.mp (norm_pos_iff.mp (g.trans_le u))
 have hu:= hv; rw [←p.1,←p.2.1,←p.2.2] at hv
 refine ⟨v,A,B',q,hv,fun n=>?_⟩; have hp: inner ℂ Ωb Ωb=1:=by rw [inner_self_eq_norm_sq_to_K,vocation_norm]; simp
 constructor <;> intro h
 · simp only [h,inner_smul_left,hp,mul_one] at hv; exact hv rfl
 simp only [h,inner_smul_right,hp,mul_one] at hv; exact hv (mul_comm ..)
-- geometry pledge all-axis
include sP tP h
variable (k L₁:Axis)(p:k≠ L₁) (hk:k≠j)(hL:L₁≠j)
local notation "X₁" a:max=> wrapped Y H k a
local notation "X₂" m:max a:max=> decant Y H k L₁ a m
local notation "γ" m:max a:max=> (X₁ a).S∪(X₂ m a).S
local notation "γf" m:max a:max=> (X₁ a).f*(X₂ m a).f
include p hk hL
lemma shipped (v:(Ξ₀ j true) z r)(g:∀ l:Axis,∃ w:ℤ,Till K r l w S T' ∨ Till K r l w T' S): ∃ n:ℕ, let f':=Δ₀ k n F; let g':=Δ₀ k n H'; let R:= plow K k n S; let W:=plow K k n T';
    ∀ᶠ i :ℕ×ℕ in atTop, let A:=mirror K k 0 f' * (Δ₀ k i.1 (Δ₀ L₁ i.2 f')); let B:=mirror K k 0 g'* (Δ₀ k i.1 (Δ₀ L₁ i.2 g')); Actually Y H D G (T:=T) d j c x s A B (reflectedBox k 0 R ∪ plow K k i.1 (plow K L₁ i.2 R)) (reflectedBox k 0 W ∪ plow K k i.1 (plow K L₁ i.2 W)) z r:= by
 obtain ⟨n,Hlz⟩:= fuses Y H D G u t d j c x s k hk L₁ hL p.symm r h z v
 let XA:Electrum K:= ⟨plow K k n S,Δ₀ k n F,false,froll k (v.input.widen) (n:ℤ),flog K S sP k n⟩; let BA:Electrum K:=⟨plow K k n T',Δ₀ k n H',true,froll k v.certified.widen (n:ℤ),flog K T' tP k n⟩
 have χ'(w:Axis):∃z:ℤ, Till K r w z XA.S BA.S∨ Till K r w z BA.S XA.S:=by
    obtain ⟨u,h⟩:= g w; by_cases f:w=k; · subst w; exact ⟨_,h.imp (fun a=> walksJ K k (n:ℤ) a) (fun a=> walksJ K k (n:ℤ) a)⟩
    exact ⟨u,h.imp (fun a=> walksGap w k (Ne.symm f) K (n:ℤ) a) (fun a=> walksGap w k (Ne.symm f) K (n:ℤ) a)⟩
 let A:= X₁ XA; let B':= X₁ BA
 have hΓ: ∀ᶠ m:ℕ×ℕ in atTop,CircleH Y H k s (X₁ XA) (X₂ m XA) (X₁ BA) (X₂ m BA):=by
    obtain ⟨z,f|f⟩:=χ' k; exact (morning_left Y H s k L₁ p XA BA h f).mono fun m a=>a.1; exact (morning_left Y H s k L₁ p BA XA h f).mono fun m a=>a.2
 have Hv:∀ᶠ m:ℕ×ℕ in atTop,CircleH Y H L₁ s (X₁ XA) (X₂ m XA) (X₁ BA) (X₂ m BA):=by
    obtain ⟨z,f|f⟩:=χ' L₁; exact (evening_left Y H s k L₁ p XA BA h f).mono fun m a=>a.1; exact (evening_left Y H s k L₁ p BA XA h f).mono fun m a=>a.2
 have hu(a:Electrum K):∀ᶠ m:ℕ×ℕ in atTop,Detached Λ l (X₁ a).S (X₂ m a).S:= (ticketTill K k L₁ p k (Or.inl rfl) a.S a.S r).mono (fun m b=>till_phys Y H k s _ h b.choose_spec)
 dsimp only at Hlz; change ∀ᶠ m:ℕ×ℕ in atTop,FundX Y H D G d j c x s (T:=T) (γ m XA) (γ m BA) (γf m XA) (γf m BA) false z r at Hlz
 refine ⟨n,?_⟩; dsimp only; change ∀ᶠ m:ℕ×ℕ in atTop,Actually Y H D G (T:=T) d j c x s (γf m XA) (γf m BA) (γ m XA) (γ m BA) z r
 filter_upwards [Hlz,hΓ,Hv,hu XA,hu BA] with m v c₀ c₁ p₀ p₁; refine inaugurate Y H D G u t d j c x s v (fun w=>?_)
 by_cases h':w=k; · subst w; exact shunning Y H D G u t d k c x s _ _ _ _ c₀ p₀ p₁ rfl rfl rfl rfl
 by_cases e:w=L₁; · subst w; exact shunning Y H D G u t d L₁ c x s _ _ _ _ c₁ p₀ p₁ rfl rfl rfl rfl
 have hv (t x: Electrum K) (z:ℤ)(p:Till K r w z t.S x.S): slottedHere (Λ:=Λ) (l:=l) w s (γ m t) (γ m x) := slotTill Y H w s (bothGap w K (turnedGap w k (Ne.symm h') K (0:ℤ) p) (walksGap w k (Ne.symm h') K (m.1:ℤ) (walksGap w L₁ (Ne.symm e) K (m.2:ℤ) p))) h
 obtain ⟨z,g⟩:=χ' w
 exact soft_two Y H D G u t d w c x s v.input.widen v.certified.widen (A.gr.mono subset_union_left) (B'.gr.mono subset_union_left) (g.imp (hv XA BA z) (hv BA XA z))
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.shipped
