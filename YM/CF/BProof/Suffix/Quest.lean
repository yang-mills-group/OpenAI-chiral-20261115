import YM.CF.BProof.Suffix.Screw
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
-- generic shooting proof. reuse rank guesses also in true family (dummy rank guesses).
open Episode
variable {a b n d k:ℕ}
-- vines dependency. Choose seeds before. Each transition tests rotor and Δ; shift law itself not implicit. Believe.Pull.Read.Spacing. Need δ exported? caller extracts shift from β via trial limited.
variable {side:ℕ→Side}
structure Quest (side:ℕ→Side)(n a:ℕ) extends Air n a where
 root: StarPS n → Parcel (side n)
 vertex:∀ j, Parcel (side j)→ Prop
 arc:∀ j,Parcel (side (j+1))→ Parcel (side j)→ Prop
namespace Quest
variable (M:Quest side n a)
local notation "P"=> (M.toAir)
abbrev Row (M':Quest side n a)(j:ℕ): Type := StarPS n → Parcel (side j)
abbrev OK (j:ℕ)(t:StarPS n → Parcel (side j))(u):= M.vertex j (t u)∧ (t u).βx=M.toAir.aim u j
-- steps induct underneath exact rank match. Note continuity only used under conductive parameters.
structure Song{N:Side}(v:StarPS n→Parcel N):Prop where
 torso: Continuous fun i=>(v i).βx
 lamp:LampF fun i=>(v i).F
 tax: ∀ (y:Force N)(p), Continuous fun i=>(v i).K y p
abbrev Ox(i:ℕ)(l:StarPS n→Parcel (side i))(u:StarPS n→ Parcel (side (i+1)))(R: StarPS n→ ΘS (M.z i))(t: StarPS n→ ℝ) : Prop:= ∀ z, M.toAir.θ i z=R z→ t z=guess_Q n M.W z i → M.arc i (u z) (l z)
structure Ready:Prop where
 low:a ≤  n
 high:Song M.root -- `M.Song` implicitly? defined when M unused => unnamespaced argument. fix
 hc:∀ z,M.OK n M.root z
 turn(j:ℕ):a ≤  j→ j<n →∀ V:StarPS n→ Parcel (side (j+1)), Song V→ (∀ z,M.OK (j+1) V z)→∃ (t: M.Row j)(f: StarPS n→ ℝ)(F: StarPS n→ ΘS (M.z j)), Song t ∧ Continuous f∧ Continuous F∧ (∀ z,|f z| ≤ M.W j) ∧ (∀ z,M.OK j t z) ∧ M.Ox j t V F f -- note `.Row` requires type binder n
-- growing trial family
structure Woven (k:ℕ)(R:∀ j, StarPS n→ Parcel (side j))(F0:ℕ→ StarPS n→ℝ)(v:∀ j:ℕ, StarPS n→ ΘS (M.z j)) : Prop where
 tall:R n=M.root
 point(j:ℕ): k ≤ j → j≤ n → Song (R j) ∧ ∀ z,M.OK j (R j) z
 step(j:ℕ):k≤j→ j<n → M.Ox j (R j) (R (j+1)) (v j) (F0 j)
 fire(j:ℕ): Continuous (F0 j) ∧ Continuous (v j)∧∀ z,|F0 j z|≤ M.W j
variable (u:M.Ready)
include u
lemma loom(j:ℕ)(p:a+j≤ n): ∃ R F v,M.Woven (n-j) R F v:=by
 induction j with
 |zero=>
    let Z : ∀ j:ℕ, StarPS n → Parcel (side j):=fun k _=>⟨0,0,0,0⟩
    let V:= update Z n M.root
    have he:V n=M.root:=update_self ..; refine ⟨V, (fun j z=> 0), M.toAir.θ,⟨he,fun j h w=>?_,fun j h v=>by omega,fun j=>⟨continuous_const,ts_θ ..,fun z=> (abs_zero).trans_le (M.toAir.hp j).le⟩⟩⟩
    rw [show j=n from by omega,he]; exact ⟨u.high,u.hc⟩
 |succ j ih=>
    let i:= n-(j+1); have he:n-j=i+1:=by unfold i; omega; -- indent ;
    have hx:i < n:=by omega
    obtain ⟨R,F,v,w⟩:= ih (by omega); have y:= w.point (i+1) he.le (by omega); obtain ⟨t,g,v',hg,pg,pv,vg,h,q⟩:= u.turn i (by omega) hx _ y.1 y.2
    let Y:=update R i t; let Z:= update F i g; let U:= update v i v';
    have hE:Y i=t:=update_self ..; have hZ:Z i=g:=update_self ..; have hU:U i=v':=update_self ..;
    refine ⟨Y,Z,U,(update_of_ne hx.ne' ..).trans w.tall,?_,?_,?_⟩
    · intro j (l:i ≤ j) s; rcases eq_or_ne j i with r|r; subst j; rw [hE]; exact ⟨hg,h⟩
      rw [show Y j=R j from update_of_ne r ..]; exact w.point j (by omega) s
    · intro j (l:i ≤ j) ht; rw [show Y (j+1)= R (j+1) from update_of_ne (by omega) ..]; rcases eq_or_ne j i with r|r; subst j; rw [hE,hZ,hU]; exact q
      rw [show Y j = R j from update_of_ne r .., show U j=v j from update_of_ne r ..,show Z j= F j from update_of_ne r ..]; exact w.step _ (by omega) ht
    intro j; rcases eq_or_ne j i with r|r; subst j; rw [hZ,hU]; exact ⟨pg,pv,vg⟩
    rw [show U j=v j from update_of_ne r ..,show Z j= F j from update_of_ne r ..]; exact w.fire j
structure Ship (v:StarPS n)(L:∀ j,Parcel (side j)) : Prop where
 orbit:L n=M.root v
 fee(j:ℕ): a ≤ j → j≤ n → M.vertex j (L j)∧ (L j).βx= M.toAir.aim v j
 anchor(j:ℕ): a ≤ j → j<n → M.arc j (L (j+1)) (L j)
theorem sail : ∃ L z,M.Ship z L:=by
 have h:= u.low; obtain ⟨R,F,v,w⟩:= loom M u (n-a) (by omega); obtain ⟨z,hz⟩:= Air.shoot P v F (fun j=>(w.fire j).2.1) (fun j=>(w.fire j).1) (fun j=>(w.fire j).2.2)
 exact ⟨fun j=>R j z,z,congrFun w.tall z,fun j v x=>(w.point j (by omega) x).2 z,fun j v x=>w.step j (by omega) x z (hz j x).1 (hz j x).2⟩
end Quest
end Cupboard
end YM.CF.Py
