import YM.CF.Vp929.Budget.Offset
import YM.CF.Haro.Cubit
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
section
namespace Plum
variable {I:Type} [Fintype I][LinearOrder I]{P : Op I}{y : Wave I}
local notation "Ur"=> LeanV I
local notation "S0"=> Finset I
local notation "Bξ"=> Finset (LeanV I)
variable {B:Finset (LeanV I)}{S: Finset I}
structure permit (S:S0)(X:Bξ) : Prop where
 down(i:I): (false,i)∈ X → i∈ S
 up(i:I): (true,i)∈ X → i∉ S
def mark (S:S0)(X:Bξ):S0:= univ.filter fun i=> (i∈S∧(false,i)∉ X)∨ (true,i)∈X
lemma markP (i:I) : i∈mark S B↔(i∈S∧(false,i)∉B)∨ (true,i)∈B:=by simp only [mark,mem_filter,mem_univ,true_and]
lemma permIn {B':Bξ}(t:B ⊆ B')(p:permit S B'):permit S B:= ⟨fun i w=>p.down _ (t w),fun i w=>p.up _ (t w)⟩
lemma permUnique {B':Bξ}(p:permit S B)(v:permit S B')(w:mark S B=mark S B'): B=B':=by
 have hz(i:I) : i∈mark S B↔i∈mark S B':=by rw [w]
 ext ⟨x,i⟩; have e:=hz i; simp only [markP] at e; by_cases hi:i∈S <;> cases x; exact (by have q:=p.up i; have h:= v.up i; tauto); exact (by have q:=p.up i; have h:=v.up i; tauto); exact (by have q:=p.down i; have h:=v.down i; tauto); exact (by tauto)
local notation "C₀" v:max=> Fock.cutM v
local notation "tag_" v:max F:max=> column (I:=LeanV I) (drawT (C₀ v)) F
local notation "key" k:max=> basisKet k
local notation "K₀" B:max=> key (mark S B)
private lemma tokens (S:S0)(i: I) : drawT (cutM S) ((false,i):Ur)=(if i∈ S then takeF i else 0) ∧ drawT (cutM S) (true,i)=if i∈ S then 0 else Fock.put i:=by
 change Fock.prong Fock.takeF (cc _) _=_∧ Fock.prong Fock.put (1-cutM S) i =_
 rw [prong_t,prong_p, act_sub,act_one,Fock.cut_basis]; by_cases h:i∈ S <;> simp [h, Fock.remove]
private lemma glyphStep (i:Ur)(v:i∉B): tag_ S (insert i B)=Fock.parity i B • (drawT (C₀ S) i * tag_ S B):=(nursery (Fock.cutM S) (Fock.cutM_idp S)).tag_any B i v
private lemma renameUp {i:I}(v:i∉ S): mark S (insert (true,i) B) = insert i (mark S B):=by
 ext d; simp only [markP,mem_insert]; by_cases p:d=i; · subst d; simp
 simp [p]
private lemma renameDown {i:I}(p:permit S B)(v:i∈ S): mark S (insert (false,i) B)= (mark S B).erase i:=by
 ext d; simp only [markP,mem_erase,mem_insert]; by_cases h:d=i; · subst d; simp [show (true,i) ∉ B from (fun x=>p.up i x v)];
 simp [h]
lemma glyph (S:S0)(B:Bξ)(h:permit S B):∃ c:ℂ,c≠0∧acts (tag_ S B) (key S)= c • key (mark S B):=by
 induction B using Finset.induction_on with
 | empty=> refine ⟨1,one_ne_zero,?_⟩; rw [show mark S ∅=S from ?_]; simp [Scree.column]; ext; simp [markP]
 | insert u B g ih=>
    let P₀:= permIn (subset_insert u B) h; obtain ⟨c,hc,E⟩:=ih P₀; let i:=u.2; have he:u∉ B:=g; let K:= mark S B; refine ⟨Fock.parity u B*(c*Fock.parity u.2 K),by unfold Fock.parity; exact mul_ne_zero (by simp) (mul_ne_zero hc (by simp)) ,?_⟩
    rw [glyphStep u g,act_smul,act_mul,E,map_smul]; clear i; rcases u with ⟨x,i⟩; cases x
    · have e:= h.down i (mem_insert_self _ _); have ht:i∈ mark S B:= (markP _).2 (Or.inl ⟨e,he⟩); rw [(tokens S i).1]
      rw [if_pos e,take_act, if_pos ht,smul_smul,smul_smul,renameDown P₀ e,mul_assoc] <;> rfl
    have e:=h.up i (mem_insert_self _ _); have ht:i ∉ mark S B:= fun p=> (markP _|>.1 p).elim (fun v=>e v.1) he; rw [(tokens S i).2, if_neg e, put_act,if_neg ht,renameUp e,smul_smul,smul_smul,mul_assoc] <;> rfl
lemma noGlyph (S:S0)(B:Bξ)(p:¬permit S B):acts (tag_ S B) (key S)=0:=by
 induction B using Finset.induction_on with
 | empty=> exact False.elim (p ⟨by simp, by simp⟩)
 | insert u B k ih=>
    rw [glyphStep u k,act_smul, act_mul]; by_cases g:permit S B; swap; · rw [ih g,map_zero,smul_zero]
    rcases u with ⟨x,i⟩; cases x
    · have he:i∉ S:=by
         intro t; apply p; constructor
         · intro j v; rw [mem_insert] at v; rcases v with e|e; exact (Prod.mk.inj e).2 ▸ t; exact g.down j e
         intro j v; rw [mem_insert] at v; exact g.up j (v.resolve_left (by simp))
      rw [(tokens S i).1,if_neg he,act_zero,smul_zero]
    have he:i∈ S:=by
       by_contra t; apply p; constructor
       · intro j v; rw [mem_insert] at v; exact g.down j (v.resolve_left (by simp))
       intro j v; rw [mem_insert] at v; rcases v with e|e; exact (Prod.mk.inj e).2 ▸ t; exact g.up j e
    rw [(tokens S i).2, if_pos he, act_zero,smul_zero]
-- diagonal crumb reading
lemma crumb_zero (F:ribbon I)(p:acts (tank (cutM S) F) (key S)=0)(u:permit S B):Pastry.crumb F.val B=0:=by
 let c:=mark S B; have e:= congrArg (inner ℂ (key c)) p; rw [tank,act_sum,inner_sum,Finset.sum_eq_single B] at e
 · obtain ⟨z,h,H⟩:= glyph S B u; rw [act_smul,inner_smul_right,H,inner_smul_right, inner_zero_right,basis_inner] at e; simpa only [show mark S B=c from rfl,basis_apply,ite_true,mul_one,mul_eq_zero, h,or_false] using e
 · intro i _ h; by_cases g:permit S i
   · obtain ⟨z,hz,H⟩:=glyph S i g; rw [act_smul,inner_smul_right,H,inner_smul_right,basis_inner,basis_apply,if_neg,mul_zero,mul_zero];
     exact fun e=> h (permUnique g u e.symm)
   rw [act_smul,noGlyph S i g,smul_zero,inner_zero_right]
 exact fun e=> (e (mem_univ _)).elim
lemma projected0 (F:ribbon I)(p:acts (tank (cutM S) F) (key S)=0):(1-cutM S)*orbitPH F*(cutM S)=0:=by
 have he(i j:I)(p':i∉S)(g:j∈S):(orbitPH F) i j=0:=by
    unfold orbitPH; rw [Matrix.of_apply,Prism.port_eq]; let B:Bξ:={(true,i),(false,j)}; have hp:permit S B:= ⟨ fun k h=> (by have h0:k=j:=(by simpa [B] using h); exact h0 ▸ g), fun k h=> (by have h0:k=i:=(by simpa [B] using h); exact h0 ▸ p')⟩
    split; rfl; rw [show crumb _ _= _ from crumb_zero F p hp,mul_zero]
 ext i j; rw [sub_mul,one_mul, sub_mul]; simp only [Fock.cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.sub_apply]
 by_cases p':i∈S; simp [p']; by_cases q:j∈S; simp [p',q,he _ _ p' q]; simp [q]
end Plum
end
end Test
end YM.CF.Py.Rate
