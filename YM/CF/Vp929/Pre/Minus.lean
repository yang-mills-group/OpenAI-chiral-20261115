import YM.CF.Vp929.Pre.Seeds
import YM.CF.Vp929.Pre.Ambit
import YM.CF.Vp929.Pre.Currency
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'

open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
open Engine Engine.Basin Engine.Docket Dialect
local notation "T_"=> Troupe S' z' (Words S')
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "De"=> T_→ Lo→ Raid D'
local notation "PZ"=> T_→Lo→ Orbit ι→ Cipher ι
local notation "oWell"=> o.muster
local notation "Loχ"=> Palot.leaf (Site (Domain m B))
local notation "Px"=> V_→Loχ→ Orbit ι→ Cipher ι
local notation "Kx"=> V_→ Loχ→ Raid (Scree.Dwell ι)
open Vow Bake Salt Stax Sour Larch
local notation "Θ'" t:max=> (cook S' (Finset.toLeft t)).flags
local notation "δ_"=> (cipherK J.n)
local notation "U_"=> (fullD (n:=ι))
variable {t bL σ κ Bv:ℝ}{nₐ:ℕ}{pW:WindV K.j 2}
variable {Z:Cellar N0 o p p' c f ag Cg} {M:Climate D.pilot R c x t bL σ κ ag Cg Bv nₐ}
namespace Focus
variable (Uq:Focus Z M pW ff)(Ty:Ids (Scree.mid m B))
local notation "Upp"=> ((tolQ p).supportExponent)
variable (Q:β∈ Year R x)(hF:Charged p' w.input K.j R.L.val h f F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> Xs β
local notation "F_"=> (Z.toLid.crew β Q).1
local notation "A0"=> (Z.toLid.choice Q (gross_shape hF (le_refl f)))
variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}

local notation "U_ν"=> value_ R x κ
lemma Seed.minus (p₀:Seed p Lz)(L:Px)(p₁:Seed p L): Seed p (Lz-L):= by
 refine ⟨fun i O h=>?_⟩; let P₀:=p₀.spruce i O h; let P₁:=p₁.spruce i O h; let A:=P₀.theme; let B:=P₁.theme; let I:= Θ' i
 refine ⟨⟨fun u v hu p=> congrArg₂ (fun v (u:Cipher ι)=> v-u) (A.same u v hu p) (B.same u v hu p),fun x=>?_ , A.keeps.sub B.keeps,fun i j=>(congrArg₂ (fun v (u:Cipher ι)=> v-u) (A.gaugeX i j) (B.gaugeX i j)).trans (map_sub ..).symm⟩,fun x V t=> congrArg₂ (fun v (u:Cipher ι)=> v-u) (P₀.turf x V t) (P₁.turf x V t),fun h p=>?_ ,fun V h=>?_⟩
 · have hu:=A.lit x; have he:=B.lit x; change Flour _ (((Lz i O x).val)-((L i O x).val)); rw [sub_eq_add_neg, ← neg_one_smul ℂ]; exact hu.add (he.smul _)
 · change Lz i O - L i O=0; rw [P₀.readV h p,P₁.readV h p,sub_self]
 change Lz i O V-L i O V≠0 at h; by_cases p:L i O V=0; rw [p,sub_zero] at h; exact P₀.lives V h; exact P₁.lives V p
lemma coneSub(Q:PZ): cone_f (Lz - Q) = cone_f Lz-cone_f Q :=by funext i D; unfold cone_f; simp only [Pi.sub_apply,sum_sub_distrib]
lemma vintage(Q:PZ): old_Q (Lz -Q) = old_Q Lz-old_Q Q:= by funext i; unfold old_Q; simp only [Pi.sub_apply,sum_sub_distrib]
lemma Placement_sub (o:Pitching w D x)(Q:PZ): Placement o Ty (Lz-Q) = Placement o Ty Lz-Placement o Ty Q:=by unfold Placement sunY; funext i v; simp only [Pi.sub_apply,Finset.sum_apply,sum_sub_distrib]
lemma Spirit.minus (p₀:Spirit p o Lz Ty)(L:PZ)(p₁:Spirit p o L Ty): Spirit p o (Lz-L) Ty:=by
 have hE(n:Side)(H T:Pax n) (h:Sym_a H)(p:Sym_a T):Sym_a (H-T):= fun t X V=>(congrArg₂ (fun v (u:Cipher n)=>v-u) (h ..) (p ..)).trans (map_sub ..).symm
 refine ⟨p₀.seed.minus L p₁.seed, by rw [coneSub]; exact hE _ _ _ p₀.musk p₁.musk, by rw [coneSub]; exact Cash.zealSub p₀.zeal p₁.zeal, by rw [vintage]; exact hE _ _ _ p₀.oak p₁.oak, ?_⟩
 rw [Placement_sub]; have he(G F:RegBudget ι): numbD (G-F)=numbD G-numbD F:=by
    funext i V; unfold numbD; simp only [comp_apply, Pi.sub_apply, deadP];
    change _-grab_A (G i V-F i V)= G i V-grab_A (G i V) - (F i V-grab_A (F i V)); rw [map_sub]; abel
 intro s; rw [he,show ∀ x y:RegBudget ι,base_Q s (x-y)=base_Q s x-base_Q s y from fun x y=> funext fun i=>funext fun z=> map_sub .., p₀.numb s,p₁.numb s]
lemma hoistAdd {a b:ℝ}(h0κ:Harvest p h κ a Lz Cp)(Q:PZ)(T:De)(s:Harvest p h κ b Q T) : Harvest p h κ (a+b) (Lz+Q) (Cp+T):= by
 refine ⟨add_nonneg h0κ.nonnegative s.nonnegative,fun i m X w=> ?_,fun i O U p t o h v=>?_⟩
 · intro v; have h0:=add_le_add (h0κ.meter i m X w) (s.meter i m X w); unfold BudgetPoint.mass at *; simp_rw [Pi.add_apply,mul_add,sum_add_distrib,add_mul,mul_add,sum_add_distrib]; exact h0
 exact Prism.tack (h0κ.hoist i O U p t o h v) (s.hoist i O U p t o h v)
lemma hoistScale(z:ℂ){a:ℝ}(u:Harvest p h κ a Lz Cp): Harvest p h κ (‖z‖*a) (z • Lz) (‖z‖ • Cp) := by
 refine ⟨fun i O j=> mul_nonneg (norm_nonneg _) (u.nonnegative i O j),fun i m X w=> ?_,fun i O U p t o h v=> Mew.grade_unit z o (u.hoist i O U p t o h v)⟩
 intro v; let H:= mul_le_mul_of_nonneg_left (u.meter i m X w) (norm_nonneg z); simp_rw [BudgetPoint.mass,Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖z‖,←mul_sum ,mul_left_comm _ ‖z‖,←mul_sum]; rw [mul_assoc]; exact H
end Focus
end Pitching
end YM.CF.Py.Rate
