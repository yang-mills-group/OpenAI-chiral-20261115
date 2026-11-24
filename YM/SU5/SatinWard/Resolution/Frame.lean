import YM.SU5.SatinWard.Resolution.PseudoSpin
import YM.SU5.SatinWard.Resolution.FF
import YM.SU5.SatinWard.Resolution.Column

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
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
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

def scaleBasis (q h:ℝ): ArcΦ→ₗ[ℝ] ArcΦ:= LinearMap.prodMap (q • LinearMap.id) ((q/h^2) • LinearMap.id)
lemma scaleBasis_eq (q h:ℝ) (i:ArcΦ):scaleBasis q h i=(q • i.1,(q/h^2) • i.2):=rfl

/-- A basis of income shapes, with uniform charge and spin support enabling actual `αPrice`.
`fourth` false for weight-three (X) scheme, true for weight-four (ℓ) scheme. Split FF keys
individually. -/
structure ResolutionFrame(ι:Type)[Fintype ι][DecidableEq ι] where
 fourth : Bool
 colors (n:Side) : SweepSign n
 grows {n m:Side}(G:Ratio n m): Grows G (colors n) (colors m)
 kills (n:Side) : (colors n).KillsScalar
 code : Coords ι →ₗ[ℝ] ArcΦ
 inj : Injective code
 representation (A:ArcΦ) (h q:ℝ)(n:Side)(p:0<q)(u:1≤h):
      (InΦ A∧(colors n).Eigenspace A)↔ A∈ LinearMap.range ((scaleBasis q h).comp code)
 polar(A):let a:=code A; (if fourth then a.2.1=0 else a.1=0 ∧ a.2.2=0)
 gauge : ι→Bool
 gauge_weight(i)(h:gauge i=true):fourth=true
 basis(i:ι):if gauge i then (code (leg i)).2=0 else (code (leg i)).1=0

-- amortized constants in Shape bounds before h/Preparation
lemma ResolutionFrame.price (F:ResolutionFrame ι) : ∃ C:ℝ, 1 ≤ C ∧ ∀ x,
     ‖F.code x‖ ≤ C* ‖x‖ ∧ ‖x‖≤ C* ‖F.code x‖:=by
 let K:= F.code.toContinuousLinearMap; let a:=‖K‖
 obtain ⟨v,t,w⟩:= F.code.injective_iff_antilipschitz.mp F.inj
 refine ⟨max (v:ℝ) (max a 1),(le_max_right ..).trans (le_max_right ..),fun x=>?_⟩
 have h:= K.le_opNorm x; refine ⟨h.trans (mul_le_mul_of_nonneg_right ((le_max_left a 1).trans (le_max_right ..)) (norm_nonneg x)),?_⟩
 apply (K.bound_of_antilipschitz w x).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _)) -- tune

private lemma scale_comm (s:ℝ)(A:EndC)(x:SU.E)(h:Commute A (SU.matter x).val):Commute (s • A) (SU.matter x).val:=by unfold Commute SemiconjBy; rw [Matrix.smul_mul,Matrix.mul_smul,h.eq]

def chiralModule : Submodule ℝ EndC where
 carrier:={x| ChiralX 0 x}
 add_mem' {x y} h v:=⟨fun g=>(h.1 g).add_left (v.1 g),by rw [star_add,h.2,v.2]⟩
 smul_mem' r x h:=⟨fun g=>scale_comm r x g (h.1 g),by rw [star_smul,star_trivial,h.2]⟩
 zero_mem':=⟨fun _=> Commute.zero_left _,star_zero _⟩
def silentModule : Submodule ℝ EndC where
 carrier:={x| WindingSpin x}
 add_mem' {x y} h v:=⟨fun g=>(h.1 g).add_left (v.1 g),by rw [cc_add,h.2,v.2]⟩
 smul_mem' r x h:=⟨fun g=>scale_comm r x g (h.1 g),by rw [cc_rsmul,h.2]⟩
 zero_mem':=⟨fun _=>Commute.zero_left _,cc_zero⟩

noncomputable abbrev Θc:=Module.finBasis ℝ chiralModule
noncomputable abbrev Θp:=Module.finBasis ℝ silentModule
abbrev Wage3:=Fin (Module.finrank ℝ chiralModule)
abbrev WageP:=Fin (Module.finrank ℝ silentModule)
abbrev Wage4:=Sum Bool WageP

lemma Kron_move (r:ℝ)(i:Axis)(A:EndC): petal i⊗ₖ (r • A)=r • (petal i⊗ₖ A):=by simp only [←Complex.coe_smul,op_kron_smul]
lemma Kron_add (i:Axis)(A B:EndC): petal i⊗ₖ (A+B)=petal i⊗ₖ A+petal i⊗ₖ B:=Matrix.kronecker_add ..

def palX (v:Axis):chiralModule→ₗ[ℝ] ArcΦ where
 toFun x:=spinShape v (↑x)
 map_add' x y:= by refine Prod.ext (add_zero _).symm (Prod.ext (Kron_add ..) (add_zero _).symm)
 map_smul' r x:=Prod.ext (smul_zero ..).symm (Prod.ext (Kron_move ..) (smul_zero ..).symm)
def ψSend(v:Axis):Coords Wage3 →ₗ[ℝ]ArcΦ:= (palX v).comp Θc.equivFun.symm.toLinearMap
lemma code_money(v:Axis)(x:chiralModule)(h q:ℝ): scaleBasis q h ((palX v) x) = palX v ((q/h^2) • x):=by rw [map_smul]; exact Prod.ext (by change q • (0:Skate)=_; simp [palX, spinShape]) rfl
lemma pulse_at(v w:Axis)(A: EndC): ChiralX v A↔ChiralX w A:=by constructor<;> exact fun t=>⟨t.1,t.2⟩

def spinFrame (v:Axis) : ResolutionFrame Wage3 where
 fourth := false
 colors n := spinCharacter n v
 kills n:= spin_no_offset n v
 grows G:=grows_spin G v
 code:= ψSend v
 inj := by
    apply Injective.comp (_:Injective (palX v)) Θc.equivFun.symm.injective
    intro x y h; exact Subtype.ext (spa_i v (congrArg (fun z:ArcΦ=>z.2.1) h))
 representation A h q n p u := by
    rw [current_sector]; constructor
    · rintro ⟨F,rfl,w⟩; let s:= q/h^2; have he: 0<s:=by unfold s; positivity
      let Y:chiralModule:=⟨F,(pulse_at v 0 F).1 w⟩
      refine ⟨Θc.equivFun (s⁻¹ • Y),?_⟩; change scaleBasis q h ((palX v) (Θc.equivFun.symm (Θc.equivFun (s⁻¹ • Y))))=_; rw [Θc.equivFun.symm_apply_apply,code_money,smul_inv_smul₀ he.ne' Y]; rfl
    rintro ⟨F,rfl⟩; let X:= (q/h^2) • Θc.equivFun.symm F; refine ⟨X.val, code_money .., (pulse_at 0 v X.val).1 X.property⟩ -- coe defeq
 polar _:=by simp; constructor<;> rfl
 gauge _:= false
 gauge_weight _ h:= by contradiction
 basis i := by rw [if_neg (by decide)]; rfl

abbrev SpruceModule := (ℝ×ℝ) × (silentModule)
def jointKey (x y:ℝ) (A:EndC):ArcΦ:=(cloverKey x y,axialSchedule A)
lemma jointSector (n:Side) (X:ArcΦ):
     (InΦ X∧(pseudoCharacter n).Eigenspace X)↔∃ Z:SpruceModule,X=jointKey Z.1.1 Z.1.2 Z.2.val:=by
 constructor
 · rintro ⟨⟨h,v,w⟩,p⟩; obtain ⟨x,y,e⟩:=(clover_sector n X.1).1 ⟨h,fun s t=>congrArg Prod.fst (p s t)⟩; obtain ⟨a,hA,pA⟩:=(axial_sector n X.2).1 ⟨v,w,fun s t=>congrArg Prod.snd (p s t)⟩; exact ⟨((x,y), ⟨a,pA⟩),Prod.ext e hA⟩
 rintro ⟨⟨⟨x,y⟩, ⟨A,h⟩⟩,rfl⟩; obtain ⟨s,v,w⟩:= (axial_sector n (axialSchedule A)).2 ⟨A,rfl,h⟩; exact ⟨⟨clover_verc x y,s,v⟩,fun g p=>Prod.ext (clover_in x y n g p) (w g p)⟩

lemma axial_add (A B:EndC): axialSchedule (A+B)=axialSchedule A+axialSchedule B:=by apply Prod.ext (add_zero _).symm; refine Prod.ext (funext fun i=>Kron_add ..) (funext fun i=>?_); change petal i⊗ₖ star _= _ ; rw [star_add,Kron_add]; rfl
lemma axial_move(r:ℝ)(A:EndC): axialSchedule (r • A)=r • axialSchedule A:=by apply Prod.ext (smul_zero ..).symm; refine Prod.ext (funext fun i=> Kron_move ..) (funext fun i=>?_); change petal i⊗ₖ star _= _; rw [star_smul,star_trivial,Kron_move]; rfl
noncomputable def craftW:SpruceModule→ₗ[ℝ] ArcΦ where
 toFun Z := jointKey Z.1.1 Z.1.2 Z.2.val
 map_add' x y:=by refine Prod.ext ?_ (axial_add ..); unfold jointKey cloverKey; simp only [Prod.fst_add,Prod.snd_add,add_smul]; abel
 map_smul' r x:=by refine Prod.ext ?_ (axial_move ..); change cloverKey (r*x.1.1) (r*x.1.2)=r • (cloverKey _ _); unfold cloverKey; rw [smul_add,mul_smul,mul_smul]
lemma unboost(q h:ℝ) (x:SpruceModule): scaleBasis q h (craftW x)=craftW (q • x.1,(q/h^2) • x.2):=by
 refine Prod.ext ?_ (axial_move ..).symm; change q • cloverKey x.1.1 x.1.2=cloverKey (q*x.1.1) (q*x.1.2); unfold cloverKey; rw [mul_smul,mul_smul,smul_add]
-- choose explicit decomp so boolean.
def fromPip (x:Coords Wage4):SpruceModule:= ((x (.inl true),x (.inl false)), Θp.equivFun.symm (x ∘ Sum.inr))
def toPip (x:SpruceModule):Coords Wage4:= Sum.elim (fun i=> if i then x.1.1 else x.1.2) (Θp.equivFun x.2)
noncomputable def pipEquiv : (Coords Wage4) ≃ₗ[ℝ] SpruceModule where
 toFun:=fromPip
 invFun:=toPip
 left_inv x:=by funext i; cases i with | inl i=> cases i <;> rfl| inr i=>change Θp.equivFun (Θp.equivFun.symm _) i=x _; rw [LinearEquiv.apply_symm_apply]; rfl
 right_inv x:= by refine Prod.ext (Prod.ext rfl rfl) (Θp.equivFun.symm_apply_apply x.2)
 map_add' x y:=Prod.ext (Prod.ext rfl rfl) (by change Θp.equivFun.symm ((x ∘ Sum.inr)+(y ∘ Sum.inr))= _; rw [map_add]; rfl)
 map_smul' r x:=Prod.ext (Prod.ext rfl rfl) (by change Θp.equivFun.symm (r • (x ∘ Sum.inr))=_; rw [map_smul]; rfl)
noncomputable def coinSend: Coords Wage4 →ₗ[ℝ] ArcΦ:= craftW.comp pipEquiv.toLinearMap
lemma axial_zero:axialSchedule 0=0:=by unfold axialSchedule; simp; rfl
lemma clover_zero: cloverKey 0 0=0:=by unfold cloverKey; simp
lemma coinSend_ff(g:Bool): let a:=(if g then 1 else 0:ℝ); let b:=(if g then 0 else 1:ℝ); coinSend (leg (.inl g))= jointKey a b 0:=by
 intro a b; let x:=leg (Sum.inl (β:= WageP) g); have p:(x ∘ Sum.inr)=0:=funext fun i=>by simp [x,leg,Pi.single_eq_of_ne]; -- tune
 change jointKey _ _ (Θp.equivFun.symm (x ∘ Sum.inr)).val= _; rw [p,map_zero]; apply congrArg₂ (fun a b=>jointKey a b 0); cases g<;>rfl; cases g <;> rfl -- kernel decide
lemma coinSend_silent(i:WageP): coinSend (leg (.inr i))=jointKey 0 0 (Θp i).val := by
 let x:=leg (Sum.inr (α:=Bool) i); have hp:(x ∘ Sum.inr)= leg i:= by funext v; by_cases t:v=i <;> simp [x,leg,t]
 have ht(b:Bool): x (.inl b)=0:=by simp [x,leg]; -- tune
 change jointKey (x (.inl true)) (x (.inl false)) (Θp.equivFun.symm _).val=_; rw [ht,ht,hp,show leg i= Θp.equivFun (Θp i) from ?_,Θp.equivFun.symm_apply_apply];
 funext j; by_cases t:j=i<;> simp [Θp.equivFun_self,leg,t]
 exact Ne.symm t

noncomputable def cloverFrame : ResolutionFrame Wage4 where
 fourth:=true
 colors:=pseudoCharacter
 grows:=grows_pseudo
 kills:=pseudo_no_offset
 code:=coinSend
 inj:=by
    apply Injective.comp (_:Injective craftW) pipEquiv.injective
    intro x y a; have he:=congrFun (congrFun (congrArg Prod.fst a) lowLow) highHigh; have hx:=congrFun (congrFun (congrArg Prod.fst a) rimB) rimC; apply Prod.ext
    · apply Prod.ext
      · change cloverKey _ _ lowLow _=cloverKey _ _ lowLow _ at he; simp_rw [clover_at_first] at he; simpa using congrArg Complex.im he
      change cloverKey _ _ rimB _=cloverKey _ _ rimB _ at hx; simp_rw [clover_at_second] at hx; simpa using congrArg Complex.im hx
    exact Subtype.ext (spa_i 0 (congrFun (congrArg (fun x:ArcΦ=>x.2.2.1) a) 0))
 representation A h q n p u := by
    rw [jointSector]; constructor
    · rintro ⟨x,rfl⟩; let s:=q/h^2; have he:0<s:=by unfold s; positivity
      refine ⟨pipEquiv.symm (q⁻¹ • x.1,s⁻¹ • x.2),?_⟩; change scaleBasis q h (craftW (pipEquiv (pipEquiv.symm _)))= _; rw [pipEquiv.apply_symm_apply,unboost]; change craftW (q • q⁻¹ • x.1,s • s⁻¹ • x.2)=craftW x; rw [smul_inv_smul₀ p.ne',smul_inv_smul₀ he.ne']
    rintro ⟨x,rfl⟩; exact ⟨_, unboost q h (pipEquiv x)⟩
 polar _:= by dsimp; rfl
 gauge i:=i.isLeft
 gauge_weight _ _:=rfl
 basis i:=by
    cases i; next i=>
       rw [if_pos (show (Sum.inl (β:=WageP) i).isLeft=true from rfl),coinSend_ff]
       exact axial_zero
    next i=> rw [if_neg (by simp : ¬ (Sum.inr (α:=Bool) i).isLeft=true),coinSend_silent]; exact clover_zero
end ShapeLab
end YM.CF.QuadClock
