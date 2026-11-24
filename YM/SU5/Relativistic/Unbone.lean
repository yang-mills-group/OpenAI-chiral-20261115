import YM.SU5.Relativistic.Sparkle
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
open CF.Pannier.Chancel.ScreeV
-- Credentials orienting FOUR cuts
structure Electrum (Z:Calibration) where
 S: Finset Cover
 f:Family Z
 gear:Bool
 paid: InTest Z true S true f
 gr:S.Nonempty
variable (a' b' c' d':Electrum (tent Y H))
local notation "PZ" A:max k:max z:max=> plated Y H (T:=T) j s (A).gear k z true (A).f
local notation "ZT" n:max=> Zest Y H D G d c x n
local notation "Tg"=> slottedHere (Λ:=Λ) (l:=l) j s
local notation "LQ" A:max W:max=> shifted (A).gear ((W).lower:ℝ)
local notation "RQ" A:max W:max=> shifted (A).gear ((W).upper:ℝ)
include t
lemma voluptuous (a:Tg a'.S b'.S)(b:Tg b'.S c'.S)(e:Tg c'.S d'.S): ∃ Q₁∈nhds (0:ℝ),∀ᶠ m:ℕ in atTop,∀ z:Cover,z j=0→(ZT m) Q₁ (((PZ a' m z) * (PZ b' m z))*((PZ c' m z) * (PZ d' m z))):=by
 obtain ⟨u0,p,q⟩:=slotFence j s a'.gr b'.gr a; obtain ⟨u1,r,g⟩:=slotFence j s b'.gr c'.gr b; obtain ⟨u2,d₁,d₂⟩:=slotFence j s c'.gr d'.gr e
 obtain ⟨l',z⟩:= slotLow j s a'.gr (Λ:=Λ) (l:=l); obtain ⟨w,v⟩:=slotTall j s d'.gr (Λ:=Λ) (l:=l)
 obtain ⟨W,hW,_,y⟩:=slotMake j s a'.gr l' u0 z p; obtain ⟨T₂,hC,xC,zC⟩:=slotMake j s b'.gr u0 u1 q r
 obtain ⟨A,hA,yA,zA⟩:=slotMake j s c'.gr u1 u2 g d₁; obtain ⟨B',hB,yB,zB⟩:=slotMake j s d'.gr u2 w d₂ v
 let E₀:Set ℝ:={x| (RQ a' W) x<(LQ b' T₂) x ∧ (RQ b' T₂) x< (LQ c' A) x ∧ (RQ c' A) x< (LQ d' B') x}
 refine ⟨E₀,(shift_notice (W:=W) (V':=T₂) (y.trans xC) a'.gear b'.gear).and ((shift_notice (W:=T₂) (V':=A) (zC.trans yA) b'.gear c'.gear).and (shift_notice (W:=A) (V':=B') (zA.trans yB) c'.gear d'.gear)),?_⟩
 filter_upwards [winFlight Y H D G u t d j c x s a'.gear a'.paid W hW,winFlight Y H D G u t d j c x s b'.gear b'.paid T₂ hC,winFlight Y H D G u t d j c x s c'.gear c'.paid A hA,winFlight Y H D G u t d j c x s d'.gear d'.paid B' hB] with m Q₁ Q₂ Q₃ Q₄ z h
 exact zest_p Y H D G d j c x m E₀ (clears_post Y H D G d j c x m E₀ (shifty b'.gear T₂.upper.val) (shifty c'.gear A.lower.val) (clears_groom Y H D G u t d j c x m E₀ (shifty a'.gear _) (shifty b'.gear _) (Q₁ z h) (Q₂ z h) (fun i (v:i∈E₀)=>v.1.le)) (clears_groom Y H D G u t d j c x m E₀ (shifty c'.gear _) (shifty d'.gear _) (Q₃ z h) (Q₄ z h) (fun i (v:i∈E₀)=>v.2.2.le)) (fun i (v:i∈E₀)=>v.2.1.le))
include D
lemma splinter {m:ℕ}(h:s≤ m){l l':List (Electrum (tent Y H))}(p:l.Perm l'):∃ C:ℂ,∀ n:ℕ,m≤n→∀z:Cover,∀ x:ℤ,(l.map fun i=> (PZ i m z) n x).prod=C • (l'.map fun i=> (PZ i m z) n x).prod:=by
 induction p with
 | nil=>exact ⟨1,fun _ _ _ _=> (one_smul ..).symm⟩
 | cons i _ ih=>
    obtain ⟨C,hC⟩:=ih; refine ⟨C,fun n h z x=>?_⟩; rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons, hC n h z x,Algebra.mul_smul_comm]
 | swap i k l=>
    refine ⟨Sector.grainB true true,fun n v z x=>?_⟩
    let A:=(PZ i m z) n x; let B':=(PZ k m z) n x
    have p(i:Electrum (tent Y H)):= never_paid Y H D G u t j s i.gear m z i.paid h v x
    simp only [List.map_cons,List.prod_cons]; rw [← mul_assoc, signMark K (p k).choose_spec (p i).choose_spec,Algebra.smul_mul_assoc, mul_assoc]
 | trans _ _ a b=> obtain ⟨C,e⟩:=a; obtain ⟨c,f⟩:=b; exact ⟨C*c,fun n h x z=>by rw [e n h,f n h,smul_smul]⟩
-- circulation hires no commutation assumption on output caps
structure CircleH : Prop where
 hired : ∃ x y u v : Electrum (tent Y H), List.Perm [a',b',c',d'] [x,y,u,v]∧ Tg x.S y.S∧ Tg y.S u.S ∧ Tg u.S v.S
local notation "AH" n:max z:max=>(((PZ a' n z)*(PZ b' n z))*((PZ c' n z)*(PZ d' n z)))
lemma Jury (p:CircleH Y H j s a' b' c' d'): ∃ Q₁∈nhds (0:ℝ),∀ᶠ m in atTop,∀ z:Cover,z j=0→(ZT m) Q₁ (AH m z):=by
 obtain ⟨A,B',C,Dd,P₀,h,z,v⟩:=p.hired; obtain ⟨Q₁,q,t'⟩:= voluptuous Y H D G u t d j c x s A B' C Dd h z v
 refine ⟨Q₁,q,?_⟩; filter_upwards [t',eventually_ge_atTop s] with m p₀ p w hw
 obtain ⟨D₁,z,q⟩:=p₀ w hw; obtain ⟨a,t'⟩:=splinter Y H D G u t j s p P₀
 refine ⟨fun t=>a*D₁ t, continuous_const.mul z,?_⟩; intro n h k v; dsimp only; rw [q h k v]
 let Kℓ (i:Electrum (tent Y H)):=(PZ i m w) n k
 let X:= (Kℓ A*Kℓ B')*(Kℓ C*Kℓ Dd)
 have hg: (AH m w) n k = a • X:=by
    change (Kℓ _ * Kℓ _) * (Kℓ _ * Kℓ _) = _
    unfold Kℓ X; simpa only [Kℓ,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,mul_assoc] using t' n h w k
 have p(i:Electrum (tent Y H)):=never_paid Y H D G u t j s i.gear m w i.paid p h k
 have he(i j':Electrum (tent Y H)): TestFamily K true (Kℓ i*Kℓ j'):= aux_test (((p i).choose_spec.mono (subset_union_left (s₂:=(p j').choose))).mul ((p j').choose_spec.mono subset_union_right))
 rw [hg]; exact ((audition Y H V G d c _ n).map_smul a (show Dome K from ⟨X, (he _ _).mul (he _ _)⟩)).symm
-- collapse rows and use ACTUAL Soft leases
lemma shunning (p:CircleH Y H j s a' b' c' d')(hg: Detached Λ l a'.S b'.S)(he: Detached Λ l c'.S d'.S)(A:a'.gear=false)(B':b'.gear=false)(C:c'.gear=true)(D':d'.gear=true): Soft Y H D G (T:=T) d j c x s false (a'.f*b'.f) (c'.f*d'.f):=by
 obtain ⟨Q₁,v,h⟩:= Jury Y H D G u t d j c x s a' b' c' d' p
 refine ⟨Q₁,v,?_⟩; filter_upwards [eventually_ge_atTop s,h] with m t₀ hx z hz
 obtain ⟨X,w,f⟩:=hx z hz; refine ⟨X,w,?_⟩; intro n uN r v; rw [f uN r v]; apply congrArg
 let A':= a'.f*b'.f; let B₀':= c'.f*d'.f
 have hp(i j':Electrum K): InTest K true ((i).S∪(j').S) false ((i).f*(j').f) := (i.paid.mono subset_union_left).mul (j'.paid.mono subset_union_right)
 simp only [Pi.mul_apply]; rw [A,B',C,D',plate_zero Y H D G u t j s m z (hp a' b') t₀ uN,plate_more Y H D G u t j s m z (hp c' d') t₀ uN,plate_zero Y H D G u t j s m z a'.paid t₀ uN,plate_zero Y H D G u t j s m z b'.paid t₀ uN,plate_more Y H D G u t j s m z c'.paid t₀ uN,plate_more Y H D G u t j s m z d'.paid t₀ uN,←(t.allCrossing Y H V Q u s (n-s) a'.paid b'.paid hg)]; unfold Vacancy.chart; rw [←relocate_mul,←cad_prod _ ordinate,← t.allCrossing Y H V Q u s (n-s) c'.paid d'.paid he]; rfl -- Bool.xor false
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.shunning
