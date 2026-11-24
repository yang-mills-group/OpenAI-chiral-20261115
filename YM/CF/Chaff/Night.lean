import YM.CF.Chaff.Moon
import YM.CF.Hype.Ace
import YM.CF.Ione.Mesh
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
variable {r Y V x μ b θ C' ρ:ℝ} {M:ℕ}
open Gloss Maize Ione Salt Hive Vow
private lemma Λpane (f:Sweep N)(x:Cipher N): Pastry.pane (Ione.suit_Y f x)=payZ f (Pastry.pane x):=by
 let r:= detX f.s; let b:= f.charge; let S:= Levier.spinU b f.s; let W:= prepU (castX f) S (xtra b) N; let V:= Scree.spice W r
 let L:Dough (LeanV (Single N)):= ⟨windX (b.xor r) x.val,Wtrans _ (fineShape x)⟩; change Pastry.pane (Pastry.fold V L)=_; rw [center_b]
 change crumb (windX (b.xor r) x.val) ∅=cSignX (b.xor r) (Pastry.pane x); cases b.xor r <;> rfl
lemma waxK(f: Era m) : shotV f (floorP m B p)=floorP m B p:=by apply Subtype.ext; change flashA _ (1:Pane Λ)=1; rw [revoke]; funext i; simp [Lattice.pull,Step.read] -- tune
variable (f: Era m)
local notation "sZ"=> netB m B f
lemma levelD (U:Briar m B e)(V:Pane Λ)(g:Agrees S U.val V): Agrees (linkQ f S) (shotV f U).val (flashA sZ V):=by apply Skye.flashD; rwa [show (linkQ f S).map _=S by ext; simp [linkQ,actS]] -- meta
variable {Y':Briar m B e→Cipher (CSide m B)} {M':ℝ}
include v A l pH h
lemma spoke_F (k:Inscribed K e n (linkQ f S) H Y' M') (g:∀ i, Y' (shotV f i)= suit_Y sZ (D i))(U:Pane Λ): pulseQ p R Y' P (linkQ f S) (flashA sZ U)=suit_Y sZ (pulseQ p R D P S U):=by
 have he: pingS P.threshold (sailX P (linkQ f S)) (flashA sZ U) ↔ pingS P.threshold (sailX P S) U:=by rw [show sailX P (linkQ f S)= _ from walkA sZ S (2*P.B)]; exact Salt.glowA P.threshold (sailX P S) sZ U
 by_cases u:pingS P.threshold (sailX P S) U; swap; · unfold pulseQ; rw [Set.indicator_of_notMem (show U∉_ from u), Set.indicator_of_notMem (show flashA sZ U∉_ from mt he.mp u)]; exact Eq.symm (map_zero _)
 let y:=Classical.arbitrary (Ids Λ); let V:Briar m B e:=⟨R (U,y),(A.paid _).shrink v.le⟩; have hL: Agrees S V.val U:= fare_H A pH l S U u y; have hQ:=levelD f V U hL
 rw [base_P (y:=shotV f V) p k A pH v l _ (he.mpr u) (fun i p q=>(hQ i p q).symm), base_P (y:=V) p h A pH v l U u (fun i p q=>(hL i p q).symm), g,map_sub, show Y' (floorP _ _ _)= _ from waxK p f ▸ g (floorP m B p),Λpane sZ]
 apply congrArg; apply Subtype.ext; change _ = sings _ _ _; rw [singT]; change _= twist _ (windX _ ((_:ℂ) • (1: FC _))); rw [win_c, twist_scalar,win_i,map_one]; rfl -- tune
omit v A l pH h
-- salad
abbrev δWeight(n:Side)(i:Scree.Hub n):ℝ:= (i.val.2.card:ℝ)⁻¹
def itemsF(p:0≤e)(R:Scree.Loom Λ)(F:Oil (e:=e) m B)(P:BudgetPoint)(i:Scree.Hub Λ): InkD Λ:= δWeight Λ i • pulseQ p R (F i.val.2) P i.val.2
def MarkF(p:0≤e)(R:Scree.Loom Λ)(F:Oil (e:=e) m B)(P:BudgetPoint): RegBudget Λ:= Larch.sunY univ (neatP P) (itemsF p R F P)
include v A l pH
lemma spark_D(i:Scree.Hub Λ)(F:Oil (e:=e) m B)(u:∀ x, F (linkQ f i.val.2) (shotV f x)=suit_Y sZ (F i.val.2 x))(w:Stamp m B→ℝ)(U:Pane Λ)(k:∀ i:Stamp m B,Inscribed K e n i H (F i) (w i)): itemsF p R F P (moveHub sZ i) (flashA sZ U)=suit_Y sZ (itemsF p R F P i U):=by
 change δWeight _ _ • _=suit_Y _ (δWeight _ _ • _); rw [map_smul,←spoke_F p (k _) A pH v l f (k _) u U, show δWeight Λ (moveHub sZ i)=δWeight Λ i from (by unfold δWeight moveHub; simp)]; rfl
abbrev MotionY(F:Oil (e:=e) m B):Prop:=∀ (f: Era m) (S:Stamp m B) (x:Briar m B e),F (linkQ f S) (shotV f x)= suit_Y (netB m B f) (F S x)
lemma star_M (F:Oil (e:=e) m B)(k:MotionY F)(w:Stamp m B→ℝ) (t:∀ i:Stamp m B,Inscribed K e n i H (F i) (w i))(U:Pane Λ)(i:Scree.Hub Λ): MarkF p R F P (moveHub sZ i) (flashA sZ U)= suit_Y sZ (MarkF p R F P i U):=by
 let e:=scope_q sZ; let W:=itemsF p R F P; unfold MarkF Larch.sunY; rw [Finset.sum_apply,Finset.sum_apply,sum_filter,sum_filter,map_sum]; conv_lhs => rw [←Equiv.sum_comp e]
 apply sum_congr rfl; intro j _; rw [show neatP P (e j)=e (neatP P j) from ?_]; · rw [show moveHub sZ i=e i from rfl]; simp only [Equiv.apply_eq_iff_eq]; split; exact spark_D p A pH v l f j F (k f j.val.2) _ U t; exact Eq.symm (map_zero _)
 exact Subtype.ext (Prod.ext rfl (walkA sZ j.val.2 _))
end YM.CF.Chaff
