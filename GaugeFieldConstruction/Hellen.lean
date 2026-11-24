import SatinThinYearn
import GaugeFieldConstruction.Nuts
import GaugeFieldConstruction.Tremolo
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
local notation "SX" β:max => Pitching.start (V:=V) (w:=w) p β
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
variable (Q:β∈ Year R x)(hF:Location.gross p' D f F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> SX β
local notation "F_"=> (Z.toLid.crew β Q).1
local notation "A0"=> (Z.toLid.choice Q hF)
variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}
variable (i:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)))(O:Palot.leaf (Site (Domain m B)))

local notation "zq"=> (half_lt_self J.ht)
variable {Xr:Pilot}{hp:fends p p' o β Xr}
variable (Pk:PondP V Xr x J.k J.d 105 5 (6+2))
variable {Rq:ℝ}(pT:GroV V Xr D.Z (X:=Pitching.start (w:=w) (V:=V) p β) (Y:=Pitching.input (w:=w) (V:=V) p' β F) o.SheepR o.bags o.vista hp (Z.toLid.choice Q hF) Cp Lz h Rq 1)

variable {L₁:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)) → Palot.leaf (Site (Domain m B)) → Orbit (Scree.mid m B)→ Cipher (Scree.mid m B)}{R₁:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)) → Palot.leaf (Site (Domain m B)) → Raid (Dwell (Scree.mid m B))}
local notation "RocX" => Roc (Scree.mid n B)
local notation "Gμ" => subtK (r:=z') S'
local notation "host" a:max => hostX (l:=Δ) S' a
variable {Rcostδ:ℝ}
variable (L':Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)) → Aura (Scree.mid m B) → Orbit (Scree.mid m B) → Cipher (Scree.mid m B))
-- pT pilot will be Zzoom for us. let its ledger pay C extras from differences.
variable (ht:Seed (D:=D) (x:=x) p (Lz - L')) (hm:Harvest (D:=D) (x:=x) (V:=V) (w:=w) p h κ Rcostδ (Lz-L') R₁)
open Riant
include hm ht Uq
-- generic sum over Rocs, supplies crafts E1 zoom/unzoom. filtering via costs receipt; for Treasury L' - Lz adjust sign.
lemma collapse (a:Seat (mid m B))(T:Finset (Roc (mid n B)))(hT:∀ i∈T,(S').ratio.parent i.1.val.1=a)(hX:∀ i:Aura ι,∀ j:RocX, j∈T→¬(host j).val⊆ i.val→ (Lz-L') (Gμ j) i=0) : Crafts p a (∑ i∈T, (Lz-L') (Gμ i)) h 2 (ZPay x*(Rcostδ*value_ R x κ)) := by
 let F i:= (Lz-L') (subtK (r:=z') S' i); let Zsum:=∑ i∈T, F i;
 have hp(i):Turf (F i):=by
    have he: Θ' (Gμ i)=∅:= by change (penn S' (Gμ i)).flags=∅; rw [Feu.penn_p,Feu.kflags]
    exact fun u=> (ht.spruce (Gμ i) u (he ▸ empty_subset _)).turf he
 refine ⟨fun i U y=>?_, fun i h=>?_,?_⟩
 · simp_rw [Finset.sum_apply]; exact sum_congr rfl fun j _=> hp j _ _ y
 · rw [Finset.sum_apply]; refine sum_eq_zero fun j p=>hX i j p fun v=> h (((hT j p) ▸ v (hail_o S' j))) -- replace
 let Rμ:= fee_term (D:=D) (V:=V) (x:=x) (w:=w) p h R₁
 let V_K(i:RocX)(j:Aura ι):ℝ:=Rμ i j
 let f(i:RocX)(j:Scree.Hub ι):= if j.val.1=a ∧ (host i).val⊆ j.val.2 then Stick p j (V_K i (lagE j)) else 0
 let Cp'(j):=∑ i∈T,f i j; have pK:=Z.request.boot.power; have hO:=Z.request.boot.order; have hv:=Z.request.boot.B; have hD:=D.high
 have hζ:0 ≤ ZPay x:=by unfold ZPay; have he:= pos_C; positivity
 have hg(i k):0 ≤ f i k:=by unfold f; split; exact mul_nonneg (by positivity) (fee_term_nonneg Uq hm ..); exact le_rfl
 refine ⟨Cp',fun Ty i=> ?_,fun j=> sum_nonneg fun i _=>hg i j,fun i p=>sum_eq_zero fun j _=> if_neg (fun h=> p h.1),?_⟩
 · have hh(j)(pj:j∈T):PressB (KeyUp p) i (Penned a (F j) Ty i) h (f j i):=by
       unfold Penned f; split
       next hu=>
         split
         next hx =>
            let v:= hx.2
            have he := singular_price Uq Ty ht hm j (lagE i) v
            have hq : tonK o.muster j (lagE i) v=i:=Subtype.ext (Prod.ext (by exact (hT _ pj).trans hu.symm) rfl)
            rw [hq] at he; have hh:=Hope.longer3 pK he (zero_le_one.trans hD) p.B; rw [hO] at hh; exact hh
         next hx =>
            have hx:=hX (lagE i) j pj (fun v=> hx ⟨hu,v⟩); change PressB _ _ (fun s=> (Lz-L') (Gμ j) (lagE i) (s, Ty)) _ _; simp_rw [hx]; exact Vale.rinse i _ h
       next hx=> rw [if_neg (show ¬(_∧_) from fun h=>hx h.1)]; exact Vale.rinse ..
   change PressB _ _ (Penned a Zsum Ty i) _ _; rw [show Penned a Zsum Ty i=∑ j∈T,Penned a (F j) Ty i from ?_]
   · exact prop_sum _ _ _ _ _ _ hh -- tune args
   funext U; by_cases k:i.val.1=a
   · simp only [Penned,k, ↓reduceIte]; simp only [Zsum, Finset.sum_apply] -- tune
   simp only [Penned,k,↓reduceIte,sum_const_zero]
 unfold ΩBook Cp'; simp_rw [mul_sum]; rw [sum_comm]; apply le_trans _ (mul_le_mul_of_nonneg_left (singular_4 Uq ht hm a) hζ); rw [mul_sum]
 refine le_trans (b:=∑ i∈T,ZPay x*∑ j:Aura ι with (host i).val⊆ j.val,(tolQ p).mass j.val (V_K i j)) (sum_le_sum fun i t=>?_) (sum_le_sum_of_subset_of_nonneg (fun i v=> mem_filter.mpr ⟨mem_univ _,hT i v⟩) fun i v _=> ?_) -- V_K shadows V_K Grace
 · unfold f; simp_rw [mul_ite,mul_zero]; rw [← sum_filter,mul_sum]
   let X:= univ.filter (fun j:Scree.Hub ι=> j.val.1=a∧ (host i).val⊆j.val.2); let Y:=univ.filter (fun j:Aura ι=> (host i).val⊆ j.val);
   rw [←sum_fiberwise_of_maps_to (s:=X) (t:=Y) (g:=lagE) (fun j p=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.2⟩)]
   apply sum_le_sum; intro j u; let Q:Scree.Hub ι:=⟨(a,j.val),(by exact ((hT i t) ▸ (mem_filter.mp u).2 (hail_o S' i)))⟩; let F':=X.filter fun x:Scree.Hub ι=>lagE x=j; have ht':lagE Q=j:=Subtype.ext rfl
   rw [sum_eq_single_of_mem (s:=F') Q (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl,(mem_filter.mp u).2⟩,ht'⟩)]; swap; · intro v t q; have h:v=Q:=Subtype.ext (Prod.ext (mem_filter.mp (mem_filter.mp t).1).2.1 (congrArg Subtype.val (mem_filter.mp t).2)); exact False.elim (q h)
   rw [ht']; let k:=coverNumber p.B j.val; let C:= Cp'; have hs := growth_z x (show p.B ≤ 2*radiusB x from by omega) Q (u:=fee_term_nonneg Uq hm i j); apply (mul_le_mul_of_nonneg_left hs (show 0 ≤ Tollup 2 p Q from (Real.exp_pos _).le)).trans
   rw [show (tolQ p).mass j.val (fee_term _ _ _ i j)=Tollup 4 p Q*V_K i j from ?_]
   swap;
   · unfold BudgetPoint.mass; congr 3; change p.supportExponent+1+1+1=4; rw [Z.request.boot.exponent]; norm_num
   refine le_trans (b:= ZPay x*((Tollup 2 p Q*Tollup (1/2) p Q)*V_K i j)) (le_of_eq (by unfold V_K Rμ; ring)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (fee_term_nonneg Uq hm ..)) hζ); unfold Tollup; rw [← Real.exp_add]; apply Real.exp_monotone; nlinarith only [Nat.cast_nonneg (α:=ℝ) (coverNumber p.B Q.val.2)]
 exact mul_nonneg hζ (sum_nonneg fun j _=> mul_nonneg (Real.exp_pos _).le (fee_term_nonneg Uq hm ..))
end Focus
end Pitching
end YM.CF.Py.Rate
end
