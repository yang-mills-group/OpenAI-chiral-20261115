import YM.SU5.Relativistic.RopeLimits
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{i k:ℕ→ℕ}(Q:Coherent Y H (i:=a) (k:=b) (E:=E) D i k)
variable (u:ℕ→ℕ)(T:ℕ→ Bool→Family (tent Y H)→Family (tent Y H))(t:GradesAll (i:=a) (a:=i) (k:=b) (b:=k) Y H u T)
local notation "W"=> wingspan Λ l


variable (s n:ℕ)(X:ℕ→ Finset Cover)
local notation "A" r:max=> a (i (u r))
local notation "B" r:max=> b (k (u r))

namespace Lariat
local notation "Ξ₁"=> (a ∘ i) ∘ u
local notation "π₁"=> (b ∘ k) ∘ u

-- true evaluation first. no heat in numerator or denominator. The same highest companion layout for all this family. Verify bare to horizon too. `payConfig` qualifies without mention of mark values except footprint S schedule.
local notation "Y₁" r:max f:max=> priceAt Y H s (A r) (B r) f
local notation "T₁" f:max=> rideL Y H T s f

-- full native
variable (i' k':ℕ)
def respan (s i' k':ℕ): {n:ℕ}→ Lariat (tent Y H) n→ Mark (side Y i' (s+n))
 | 0,start f=> distribute Y H s i' f.mark
 | n+1,stretch f g=> (ascender Y (s+n) i' k' (respan s i' k' f))*distribute Y H (s+n+1) i' g.mark

def dues_i (X:ℕ→ Finset Cover)(r:ℕ): Prop:= ∀ j:ℕ,j≤r→ Host Y H i' (s+j) (runningBox Λ l X j) ∧ Host Y H i' (s+j+1) (wingspan Λ l (runningBox Λ l X j))

lemma packsEnough (X:ℕ→ Finset Cover)(n:ℕ) : ∀ᶠ i in atTop, dues_i Y H s i X n:=by
 have hp(j:ℕ):= (eventually_host Y H (s+j) (runningBox Λ l X j)).and (eventually_host Y H (s+j+1) (wingspan Λ l (runningBox Λ l X j)))
 filter_upwards [(eventually_all_finset (Finset.Iic n)).2 fun i _=> hp i] with n h; intro j p; exact h j (mem_Iic.mpr p)

lemma nativeBox (f:Lariat (tent Y H) n)(p: Costs X f)(q: Tapestry.Pay Y (s+n) i' k')(v:dues_i Y H s i' X n):distribute Y H (s+n) i' (priceAt Y H s i' k' f)=respan Y H s i' k' f:=by
 induction f with
 | start f=>rfl
 | @stretch n f g ih=>
    change distribute Y H (s+n+1) i' (moveUp Y H (s+n) i' k' (box Λ l f) (hue f) _ * g.mark)=ascender Y (s+n) i' k' _*_
    have e:= v n (by omega)
    have h: Tapestry.Pay Y (s+n) i' k':=⟨q.1,Nat.le_trans (by omega) q.2⟩
    have hx:= rebased Y H (s+n) i' k' _ (show legalAt Y (s+n) i' k' from ⟨q.1,q.2⟩) (groundPrice Y H s f i' k') (by rw [show box Λ l f=runningBox Λ l X n from hires n X p.1]; exact e.2.usable 0)
    rw [(distribute_arith Y H (s+n+1) i' _ _ 1).2.1,hx,ih p.1 h (fun k p=>v k (p.trans (by omega)))]

-- all the way through bare, chiral mark still valid with grade. wide output OK. not asserting positivity for odd at s+n reaching top! parity holds for partner limit.
lemma honed {ν:ℕ}{b':Bool}{S:Finset Cover} (f:Mark (side Y i' ν)) (p: AtSupport b' (Satin.region S (side Y i' ν)) f)(z:Tapestry.Pay Y ν i' k') (r:ℕ)(h:ν+r≤Y.uv k') : ∃ F:Mark (side Y i' (ν+r)), AtSupport b' (Satin.region (volumeAround Λ l r S) (side Y i' (ν+r))) F ∧ Journey.compass Y i' k' (ν+r) F=Journey.compass Y i' k' ν f:=by
 induction r with
 | zero=> exact ⟨f,p,rfl⟩
 | succ r ih=>
    obtain ⟨F,p,h'⟩:=ih (by omega);
    let Q:= (Y.voyage i').X (Y.uv k'); let G:= (Y.voyage i').CapeT; have hx:Satin.PairIdx Y (ν+r) i' k':= ⟨z.1,h⟩ -- adjust namespace
    have hv:= fullness Y i' k' z.1
    refine ⟨Tapestry.ascender Y (ν+r) i' k' F, Tapestry.ascendSupport Y (ν+r) i' k' _ hx p,?_⟩
    rw [← h']; unfold Journey.compass
    change markedRead (Tapestry.ascender Y (ν+r) i' k' F) (G _) _/ _=markedRead F (G _) _ / _
    have e:= fermiAdvance Λ.U Q.gram G _ _ _ Q.wave _ (Journey.legal Λ) hv.cap_grant (y:=ν+r) hx.2 p
    have k: partitionZ (Q.gram (ν+(r+1))) Λ.U (G (ν+(r+1)))= partitionZ (Q.gram (ν+r)) Λ.U (G (ν+r)):= (Q.balance _ hx.2).trans (Q.balance _ hx.2.le).symm
    exact congrArg₂ (HDiv.hDiv (γ:=ℂ)) e.symm k

lemma polished (f:Lariat (tent Y H) n)(p:Costs X f)(q:Tapestry.Pay Y (s+n) i' k')(v:dues_i Y H s i' X n): let F:= priceAt Y H s i' k' f; let Z:=respan Y H s i' k' f
                 sharp Y H (s+n) i' k' F= Journey.compass Y i' k' (s+n) Z∧ microscope Y i' k' 1≠0∧
                 ∃ W₀:Mark (side Y i' (Y.uv k')),AtSupport (hue f) (Satin.region (volumeAround Λ l (Y.uv k'-(s+n)) (runningBox Λ l X n)) (side Y i' (Y.uv k'))) W₀∧
                           sharp Y H (s+n) i' k' F= (microscope Y i' k' W₀)/(microscope Y i' k' 1):=by
 intro F Z; have ht:distribute Y H (s+n) i' F=Z:= nativeBox Y H s n X i' k' f p q v
 change Journey.compass Y i' k' (s+n) _= Journey.compass Y i' k' (s+n) Z ∧ _
 have he : sharp Y H (s+n) i' k' F= Journey.compass Y i' k' (s+n) Z:= congrArg (fun g=>Journey.compass Y i' k' (s+n) g) ht
 refine ⟨he,(same_denominator Y (s+n) i' k' q.1 q.2).2,?_⟩
 let r:= Y.uv k'-(s+n)
 have hx:s+n+r=Y.uv k':=by unfold r; have h:= q.2; omega -- use q.2
 have hv:AtSupport (hue f) (Satin.region (runningBox Λ l X n) _) Z:= (show box Λ l f=runningBox Λ l X n from hires n X p) ▸ ht ▸ parked Y H (s+n) i' _ (groundPrice Y H s f i' k')
 have hh :∃ W₀:Mark (side Y i' (Y.uv k')), AtSupport (hue f) (Satin.region (volumeAround Λ l r (runningBox Λ l X n)) (side Y i' (Y.uv k'))) W₀ ∧ Journey.compass Y i' k' (Y.uv k') W₀= Journey.compass Y i' k' (s+n) Z:= by
    suffices h: ∃ F:Mark (side Y i' (s+n+r)), AtSupport (hue f) (Satin.region (volumeAround Λ l r (runningBox Λ l X n)) (side Y i' (s+n+r))) F ∧ Journey.compass Y i' k' (s+n+r) F=Journey.compass Y i' k' (s+n) Z from hx ▸ h
    exact honed Y i' k' Z hv q r hx.le
 obtain ⟨W₀,t,e⟩:= hh
 refine ⟨W₀,t,?_⟩; rw [he,←e]; unfold Journey.compass; rw [(onePrior Y i' k' W₀ t.env q.1).2,(same_denominator Y (Y.uv k') i' k' q.1 le_rfl).1]
end Lariat

end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
