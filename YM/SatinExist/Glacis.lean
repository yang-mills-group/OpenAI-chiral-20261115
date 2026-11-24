import YM.SatinExist.Crust
import SatinThinRoman
import SatinThinTrees
import SatinThinCrystal
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis.Head.Etch
variable (i k:ℕ){f r v d:ℕ}{a c:ℝ}
local notation "L"=> P.R.L
local notation "Δ"=> P.block
local notation "Ω" j:max=> side Y i j
local notation "Gξ" j:max=> Vale.apt (Y.ir i) P.block P.R.L j
open Again Buffered.Afterglow.Tower.SlabMark
variable {A b z U u:ℝ} {m j:ℕ} (p:f ≤ r)(x:r ≤ v)(l:List (Site (side Y i f)))
-- coordinates card independent of v support width
open Buffered.Afterglow.Tower
variable (w e:ℕ)(a':Axis)(x:Site (side Y i f))
-- length coverage threshold as a function of registered params. gamma a cost per gap & unmarked per-site burden remains. choose generous
abbrev spacePrice (B:Side)(w e:ℕ):ℕ:= 16 * (16*B.val*w) * (2*plusAgain B e)^3
noncomputable def truckBill (B:Side)(w e:ℕ)(c y:ℝ):ℝ:= c*Real.exp (y*↑(spacePrice B w e))
-- if sq() consumes Outer. 
lemma spin_dim {n:Side}(l:List (Site n))(p:outdoor e l): l.length≤(More n).val^4:=by
 have ht: l.Nodup:=p.imp (by intro i j h u; rw [u,separation_self] at h; omega)
 refine ht.length_le_card.trans ?_; have he: Fintype.card (Site n)=n.val^4:=by simp [Site,Four,Per,Axis]; -- check
 rw [he]; apply pow_le_pow_left'; change _≤n.val*2; omega
private lemma discovery {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
-- mast argument P^e. list pricing. Ice cost with total count. 
section
variable {F:Site (side Y i f)→ Mark (side Y i v)}{G:Mark (side Y i v)→ℂ}
variable {n j T:ℕ}{x c y:ℝ}{q:ℤ→ℤ}
local notation "ΩF"=> Ω f
local notation "ΩV"=> Ω v
local notation "Y₀"=>truckBill Δ w e c y
lemma eternal {α:ℕ}(H:0<n)
    (Z:GraceA Δ e T F G q α)
    (h:0<c)(g':0≤ y)(hy:0≤x)
    (O:∀ l:List (Site (side Y i f)),outdoor T l → ‖Journey.compass Y i k v (l.map F).prod‖ ≤ c^l.length*Real.exp (y*((More (side Y i f)).val:ℝ)^4))
    (K':∀ (Q:List (Site (side Y i f))), Envelope (Q.map F).prod)
    (p:f≤v)(u:Ferry Y v i k)(z:G=solder Y i k u.depth v)(δ:IcePlot Y v i k)
    (W:List (Site (side Y i f)))(o:outdoor T W)(V:W.length=4*n)(b:∀ a:Axis,a≠a'→ cows a (upperRoll W) 0)
    (r:∀ z:Fields (side Y i v), ‖(W.map F).prod z‖ ≤ x^(4*n))
    (d:plusAgain Δ e ≤ (side Y i f).val)(i1:(side Y i f).val ≤ 4*n * (16*P.block.val*w))
    (t:x*(16/truckBill Δ w e c y) ≤ (↑(ΩV).val:ℝ)):
     ‖G (W.map F).prod‖ ≤ (2*truckBill Δ w e c y)^(4*n) :=by
 let N:= Ω f; let U':= F; let B:= Ω v; obtain ⟨i0,hk,hi⟩:= discovery (show 0<plusAgain Δ e from plusAgain_pos) d; let J:=2^i0
 let l:= J^3; let S:= Finset.univ.erase a'
 obtain ⟨t',hq,hl,ht,h'⟩:= spun_all Z W S o (fun i w=> b i (mem_erase.mp w).1) (k:=i0) (by simpa only [Nat.zero_add] using hk) r
 have hs:S.card=3:=by simp [S,Axis] -- card erase
 rw [hs] at hl ht h'; rw [V] at hl
 let z':=t'.length; have hz:z'=l*(4*n):=hl; have hp:0<l:=by unfold l J; positivity
 have hv:0<z':=hz ▸ Nat.mul_pos hp (by omega); -- hz identity rewrite
 have hw: (More N).val^4 ≤ z' * spacePrice P.block w e:=by
    change (N.val*2)^4 ≤_
    let a:=16*P.block.val*w; let b:=plusAgain Δ e
    have he: N.val ≤ J*(2*b):= hi.trans_eq (by unfold J b; ring)
    calc
       _ = 16 * (N.val*N.val^3) := by ring
       _ ≤ 16 *((4*n * a)*(J*(2*b))^3):= by gcongr -- tune
       _ = z' * spacePrice Δ w e:=by rw [hz]; unfold spacePrice l a b; ring
 let Y':= (t'.map F).prod; let u':= Journey.compass Y i k v; let D':= truckBill Δ w e c y; have hd:0<D':=mul_pos h (Real.exp_pos _)
 have hx:‖u' Y' - G Y'‖ ≤ D'^z':=by
    have ht'(a:Fields B): ‖Y' a‖ ≤ x^z':=by rw [hz,mul_comm l _,pow_mul]; exact ht a
    rw [z]; have hp:=spin_dim T t' hq; have hb: z' ≤ (More (side Y i v)).val^4:= hp.trans (pow_le_pow_left' (Nat.mul_le_mul_right 2 (growingM Y i p)) _)
    exact (δ u.depth Y' (x^z') (K' t') ht').trans (hailW Y i hd hy t hb)
 have hg : ‖u' Y'‖ ≤ D'^z':=by
    apply (O _ hq).trans; unfold D' truckBill
    rw [mul_pow,←Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg h.le _)
    apply Real.exp_monotone; let e':= spacePrice P.block w e
    calc _≤ y*((z':ℝ)*(e':ℝ)):=by gcongr; exact_mod_cast hw
         _=_:=by unfold e'; ring
 apply (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) hd.le) _) (n:=l) hp.ne').mp
 refine h'.trans ((norm_le_norm_sub_add (G Y') (u' Y')).trans ?_)
 rw [norm_sub_rev, ←pow_mul,← hz.trans (mul_comm l (4*n)),mul_pow]
 exact (add_le_add hx hg).trans ((by rw [←two_mul]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hd.le _); simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hv) : D'^z'+D'^z' ≤ (2:ℝ)^z'*D'^z'))
end
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.eternal
