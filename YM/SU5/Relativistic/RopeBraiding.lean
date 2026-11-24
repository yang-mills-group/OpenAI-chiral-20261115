import YM.SU5.Relativistic.Rope
import YM.SU5.Relativistic.Whirl
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


variable (s:ℕ)
namespace Lariat
section prep
variable {K':Calibration}
def mate (j:Axis)(z:ℤ)(g:Ink K'): Ink K':= ⟨mirror K' j z g.mark,g.kind,reflectedBox j z g.S,axial K' _ _ g.bill⟩
def turned (Λ:Preparation)(j:Axis)(z:ℤ): {n:ℕ} → Lariat K' n→ Lariat K' n
 | _,start f=> start (mate j z f)
 | n+1,stretch f g=> stretch (turned Λ j z f) (mate j (planeAt z Λ.R.L (n+1)) g)
lemma mate_hue {n}(f:Lariat K' n)(Λ:Preparation)(j:Axis)(z:ℤ) : hue (turned Λ j z f)= hue f:=by
 induction f with| start f=>rfl| @stretch n f g h=> rw [turned,hue,h]; rfl

def pairsAt (f g:Ink K')(z:ℂ): Ink K':= ⟨z • (f.mark*g.mark),f.kind.xor g.kind,f.S∪g.S, InTest.smul _ ((f.bill.mono subset_union_left).mul (g.bill.mono subset_union_right))⟩
def glueWord : {n:ℕ} → Lariat K' n → Lariat K' n→ Lariat K' n
 | _,start f, start g=> start (pairsAt f g 1)
 | _+1,stretch f p, stretch g q=> stretch (glueWord f g) (pairsAt p q (Sector.grainB p.kind g.hue))
lemma glueHue {n}(f g:Lariat K' n): (glueWord f g).hue= (hue f).xor (hue g):=by
 induction f with
 | start f=> cases g; rfl
 | stretch f p ih=>
    cases g with| stretch g q=> change ((hue (glueWord f g)).xor (p.kind.xor q.kind)) = ((hue f).xor p.kind).xor ((hue g).xor q.kind); rw [ih]; clear ih; generalize f.hue=u; generalize g.hue=v; generalize p.kind=w; generalize q.kind=z; cases u<;>cases v<;>cases w<;>cases z <;> rfl

def standoff (Λ:Preparation)(l:ℕ): {n:ℕ} → Lariat K' n → Lariat K' n→ Prop
 | _,start _,start _=>True
 | _+1,stretch f _,stretch g _=> standoff Λ l f g ∧ Detached Λ l (box Λ l f) (box Λ l g)

def longer(f:Ink K')(v:Finset Cover)(p:f.S⊆v) : Ink K':=⟨f.mark,f.kind,v,f.bill.mono p⟩
end prep

local notation "E₀" f:max=> rideL Y H T s f
variable {n:ℕ}
include V Q t
lemma drawFlip (j:Axis)(z:ℤ)(f:Lariat (tent Y H) n): rideL Y H T s (turned Λ j z f) = mirror (tent Y H) j (planeAt z Λ.R.L n) (rideL Y H T s f) :=by
 induction f with
 | start f=> rw [planeAt,pow_zero,one_mul]; rfl
 | @stretch n f g ih=>
    rw [turned,rideL,ih, mate_hue, t.lay Y H V Q u (s+n) (aboard Y H u T t s f), step_plane,rideL,mirror_times]; rfl
lemma braided (f g: Lariat (tent Y H) n)(p:f.standoff Λ l g): E₀ (glueWord f g) = (E₀ f)*(E₀ g) :=by
 induction f with
 | start f=> cases g with | start g=> exact one_smul ..
 | @stretch n f p' ih=>
    cases g with| stretch g q =>
      have he:= p.2
      have ht := aboard Y H u T t s (n:=n)
      rw [glueWord,rideL,glueHue, ih _ p.1,t.sealPair Y H V Q u (s+n) (ht f) (ht g) he]
      let A':= T (s+n) f.hue (E₀ f); let B':=T (s+n) g.hue (E₀ g)
      let X:=p'.kind; let Y':= g.hue; let φ :=Sector.grainB X Y'
      have hv: p'.mark*B' = φ • (B'*p'.mark) := signMark (tent Y H) p'.bill (t.pays Y H u _ (ht g))
      change A'*B'* (φ • (p'.mark*q.mark))= A'*p'.mark*(B'*q.mark)
      rw [Algebra.mul_smul_comm,mul_assoc A' p'.mark (B'*q.mark),←mul_assoc p'.mark,hv,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; simp only [mul_assoc]

-- condition always holds at actual orientation B*B.
omit V Q t
lemma placedRoom {j:Axis}{z:ℤ}(f:Lariat (tent Y H) n)(p:f.ordains (Λ:=Λ) l s j z) : Tower.region j (planeAt z Λ.R.L n) ((tent Y H).ℓ) (box Λ l f):=by
 induction f with
 | start f=> rw [planeAt,pow_zero,one_mul]; exact p
 | @stretch n f g ih=>
    intro i e; rcases mem_union.mp e with a|b; · rw [←step_plane]; exact wingspan_region Y H _ j _ (ih p.1) i a
    exact p.2 i b

-- relation for two positive test ropes with same hinge: need symmetry of wingspan under reflect, stronger than Atlas earlier. derive wingspan equiv or shifted region of reflected leg. to use mirrored support `.pay`. Geometry at all heights. next
end Lariat

end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
