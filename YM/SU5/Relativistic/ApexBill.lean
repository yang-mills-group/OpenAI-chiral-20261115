import YM.SU5.Relativistic.CarryBoundary
import YM.SU5.Relativistic.TrueSeparation
import YM.SU5.Relativistic.StemRead
import YM.SU5.Relativistic.StringSignal
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
local notation "P₀" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f


open Lariat
section weights
variable (M:Panel Y H D.univ_ G.history G.clipped d false (c d)) (y:M.X)

variable (A:∀ i:ℕ, Future Y H d i)(w:ℕ→ℕ) (p: Subscribed Y H D G d c M y u T A w)
open Lariat
local notation "I₁" i:max=>a (G.rows (u (w i)))
local notation "K₁" i:max=>b (G.columns (u (w i)))
local notation "F₀" i:max=> (Future.kernelPath Y H d (A i)).val
local notation "Y'" i:max=>(A i).t
local notation "Φ" i:max=> sharp Y H (Y' i) (I₁ i) (K₁ i) (Future.kernelPath Y H d (A i)).val
local notation "R₀" s:max=>appeal Y H D G d c (M.character y) T s


section ascent
variable (x' ℓ r:ℕ)(S U:Finset Cover)
def apex (x' ℓ r:ℕ)(b':Bool) (h:Family (tent Y H))(S:Finset Cover):ℕ→Family (tent Y H)
 | 0=>h
 | n+1=> moveUp Y H (r+n) x' ℓ (volumeAround Λ l n S) b' (apex x' ℓ r b' h S n)
-- includes x' etc ensure exposed args; hZ Support record
variable {g f:Family (tent Y H)}{c' b':Bool} (z:Host Y H x' r S)(hy_:InTest (tent Y H) true S b' f)
-- apex order check, level law from fermiAdvance
local notation "L₀" S:max b:max f:max n:max=> apex Y H x' ℓ r b f S n
include z hy_
lemma apexLaw (n:ℕ)(t:Tapestry.Pay Y (r+n) x' ℓ) : InTest K true (volumeAround Λ l n S) b' (L₀ S b' f n) ∧ sharp Y H (r+n) x' ℓ (L₀ S b' f n)= sharp Y H r x' ℓ f:=by
 induction n with
 | zero=> exact ⟨hy_,rfl⟩
 | succ n ih=>
    obtain ⟨e,h⟩:= ih ⟨t.1,(by obtain ⟨k,y⟩:=t; omega)⟩
    let u:= L₀ S b' f n
    let X:=(Y.voyage x').X (Y.uv ℓ); have hv:legalAt Y (r+n) x' ℓ:=⟨t.1,t.2⟩
    refine ⟨stay ..,?_⟩
    rw [←h]; change Journey.compass Y x' ℓ (r+n+1) (distribute Y H _ _ (moveUp Y H (r+n) x' ℓ _ b' _))= Journey.compass Y x' ℓ (r+n) (distribute Y H (r+n) _ u)
    rw [rebased Y H _ x' ℓ _ hv e (z.usable (n+1))]; unfold Journey.compass
    have hu:= fermiAdvance Λ.U X.gram (Y.voyage x').CapeT _ _ _ X.wave _ (Journey.legal Λ) (fullness Y x' ℓ hv.1).cap_grant hv.2 (parked Y H (r+n) _ _ e)
    exact congrArg₂ (HDiv.hDiv (γ:=ℂ)) hu.symm ((X.balance _ hv.2).trans (X.balance _ hv.2.le).symm)
omit z hy_
lemma apex_pair (p: Detached Λ l S U)(z:Host Y H x' r (S∪U))(x:InTest (tent Y H) true S b' f)(w:InTest K true U c' g)(n:ℕ)(t:Tapestry.Pay Y (r+n) x' ℓ): apex Y H x' ℓ r (b'.xor c') (f*g) (S∪U) n = (L₀ S b' f n)*(L₀ U c' g n):=by
 -- at_step needs Host (r+n) union. get Host there via tower union volume laces.
 induction n with
 | zero=> rfl
 | succ n ih=>
    have hx:Tapestry.Pay Y (r+n) x' ℓ:= ⟨t.1,(by obtain ⟨k,h⟩:=t; omega)⟩; let T:=volumeAround Λ l n (S∪U)
    have ht:Host Y H x' (r+n) T:=by
       constructor
       · intro i; have he:= z.usable (n+i); rw [volume_add,←Nat.add_assoc] at he; exact he
       intro i; have he:= z.distances (n+i); rw [volume_add,←Nat.add_assoc] at he; exact he
    have hu:T=volumeAround Λ l n S∪volumeAround Λ l n U:=by
       unfold T; exact union_level Λ l n S U
    rw [hu] at ht
    rw [apex,ih hx,union_level]; exact together Y H (r+n) x' ℓ _ (Around_detaches _ _ p n) ht ⟨t.1,t.2⟩ (apexLaw Y H x' ℓ r S (Host.shrink Y H subset_union_left z) x n hx).1 (apexLaw Y H x' ℓ r U (Host.shrink Y H subset_union_right z) w n hx).1
where
 union_level (Λ:Preparation)(l n:ℕ)(S U: Finset Cover):volumeAround Λ l n (S∪U)=volumeAround Λ l n S∪volumeAround Λ l n U:=by
    induction n with| zero=>rfl| succ n ih=> rw [volumeAround,ih]; change wingspan _ _ (_∪_) = wingspan _ _ _ ∪ wingspan _ _ _; unfold wingspan Satin.liner; rw [Finset.image_union,Finset.union_biUnion]
end ascent

end weights
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
