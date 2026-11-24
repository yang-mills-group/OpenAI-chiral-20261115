import GaugeFieldConstruction.Elide
-- polynomial L boosts
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Py Trees Hake FlightFlux TableF Boom Axon Lenten.ModuleB Flot Taxi
open HarmP
namespace BellPrice
abbrev χleaf (R:Side):ℝ:=1+Real.log R.val
lemma ζone (R:Side):1 ≤ χleaf R:=le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast R.property))
def SlowP (f:Side→ ℝ): Prop:=∃ C:ℝ,0 ≤ C ∧ ∃ k:ℕ, ∀ᶠ R:Side in atTop, |f R|≤ C*(χleaf R)^k
namespace SlowP
variable {F G:Side→ℝ}
lemma upZ (p:SlowP F)(v:∀ᶠ L:Side in atTop,|G L|≤ |F L|):SlowP G:=by obtain ⟨c,h,n,t⟩:=p; exact ⟨c,h,n,(v.and t).mono (fun i h=> h.1.trans h.2)⟩ -- tune
lemma level (c:ℝ): SlowP (fun _=>c):=⟨|c|,abs_nonneg _,0,Eventually.of_forall (by simp)⟩
lemma prod (p:SlowP F)(v:SlowP G):SlowP (fun l=>F l * G l):=by
 obtain ⟨c,h,n,t⟩:=p; obtain ⟨b,u,m,z⟩:=v; refine ⟨c*b,mul_nonneg h u,n+m,?_⟩; filter_upwards [t,z] with l t z; rw [abs_mul]; exact (mul_le_mul t z (abs_nonneg _) ((abs_nonneg _).trans t)).trans_eq (by rw [pow_add]; ring)
lemma pots (p:SlowP F)(n:ℕ): SlowP (fun l=> F l ^ n):=by induction n with|zero=>simpa using level 1|succ i h=> simp_rw [pow_succ]; exact h.prod p
lemma join (p:SlowP F)(v:SlowP G):SlowP (fun l=>F l + G l):=by
 obtain ⟨c,h,n,t⟩:=p; obtain ⟨b,u,m,z⟩:=v; refine ⟨c+b,add_nonneg h u,n+m,?_⟩; filter_upwards [t,z] with l t z; rw [add_mul]; refine (abs_add_le ..).trans ((add_le_add t z).trans (add_le_add ?_ ?_)); · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ζone _) (by omega)) h
 exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ζone _) (by omega)) u
lemma swell: SlowP SpanL:=((level 4).prod (F:=fun _=>4) (G:=χleaf) (show SlowP χleaf from ⟨1,zero_le_one,1,Eventually.of_forall (fun i=>by rw [abs_of_nonneg (zero_le_one.trans (ζone _)),pow_one,one_mul])⟩)).pots 4 -- tune F already implicit
lemma spinNat : Tendsto (fun i:Side=> i.val) atTop atTop:=by
 apply Filter.tendsto_atTop.mpr; intro n; filter_upwards [eventually_ge_atTop (⟨n+1,by omega⟩:Side)] with i p; change n+1 ≤ (i:Side).val at p; change n ≤ i.val; omega
lemma spinReal:Tendsto (fun i:Side=> (i.val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp spinNat
lemma escapes(p:SlowP F){v:ℝ}(u:0<v):Tendsto (fun i:Side=>|F i|/(i.val:ℝ)^v) atTop (𝓝 0):=by
 obtain ⟨C,h,b,s⟩:=p; let Φ (i:Side):= Real.log (i.val:ℝ); let X (i:Side):=(i.val:ℝ)^v
 have hz(i:Side):0 < X i:= Real.rpow_pos_of_pos (by exact_mod_cast i.property) _
 let g(i:Side):= C*2^b *(Φ i ^ b / X i)
 apply squeeze_zero' (Eventually.of_forall fun i=>div_nonneg (abs_nonneg _) (hz i).le) (g:=g) ?_ ?_
 · filter_upwards [s,(Real.tendsto_log_atTop.comp spinReal).eventually_ge_atTop 1] with i s v'; have hU : χleaf i ≤ 2*Φ i:=by have ht:1 ≤ Φ i:=v'; change 1+Φ i ≤ _; linarith
   apply le_trans _ (le_of_eq (show C*(2*Φ i)^b/X i=g i from by unfold g; rw [mul_pow]; ring)); exact div_le_div_of_nonneg_right (s.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (ζone _)) hU _) h)) (hz i).le
 have ht:Tendsto (fun i=> Φ i ^ b /X i) atTop (𝓝 (0:ℝ)):=by simp only [←Real.rpow_natCast]; exact (isLittleO_log_rpow_rpow_atTop (b:ℝ) u).tendsto_div_nhds_zero.comp spinReal
 exact mul_zero (C*2^b) ▸ ht.const_mul _
end SlowP
abbrev noonFac(k:ℝ)(B:Bool→ℝ)(L:Side):ℝ:= let s:=k*SpanL L; 7* DevelopCost*shapeCost s+ Haro.flavor^2*((7:ℝ)*Haro.horn)* (3*PLuck s)*(24^3*10^3*1800*B false*B true*SpanL L^2)*(Haro.flavor^2)
lemma Nshift(k:ℝ)(B:Bool→ℝ)(R:Side)(r:ℕ)(t:ℝ)(P:BudgetPoint)(p:P.order=6) : Noon P R B (k*SpanL R) t r=noonFac k B R*(αN R)^(3+r)*t:=by unfold Noon Fee1 Kirby noonFac tape αN; rw [p]; push_cast; ring
lemma noonSlow (k:ℝ)(B:Bool→ℝ) : SlowP (noonFac k B):=by
 let s (i:Side):=k*SpanL i; let K:= Haro.flavor^2*((7:ℝ)*Haro.horn); let J:= xHoch 6
 have hs:SlowP s:= (SlowP.level k).prod SlowP.swell; have hp:SlowP (fun i=>shapeCost (s i)):= (SlowP.level _).prod ((SlowP.level _).prod (((SlowP.level _).prod hs).pots _))
 have hS:SlowP (fun i=>DepotPrice (s i)):= SlowP.join ((SlowP.level _).join (((SlowP.level _).prod hs).join (SlowP.level _))) (((SlowP.level _).prod (hs.pots _)).join (SlowP.level _)) -- tune order
 have hP:SlowP (fun i=> PLuck (s i)):= (SlowP.level _).prod (hS.join ((SlowP.level _).prod (((SlowP.level _).prod hs).pots _)))
 exact SlowP.join ((SlowP.level _).prod hp) ((((SlowP.level _).prod ((SlowP.level _).prod hP)).prod ((SlowP.level _).prod (SlowP.swell.pots _))).prod (SlowP.level _))
abbrev stipe (k:ℝ)(B:Bool→ℝ)(L:Side):= |noonFac k B L|+1
lemma stipeS(k:ℝ)(B:Bool→ℝ):SlowP (stipe k B):= ((noonSlow k B).upZ (G:=fun i=> |noonFac k B i|) (by simp)).join (SlowP.level _)
lemma stipeV(k:ℝ)(B:Bool→ℝ)(R:Side)(r:ℕ)(t:ℝ)(P:BudgetPoint)(p:P.order=6)(v:0 ≤ t) : Noon P R B (k*SpanL R) t r≤ stipe k B R*(αN R)^(3+r)*t:=by rw [Nshift _ _ _ _ _ _ p]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) (by have he:=α_pos R; positivity)) v
end BellPrice
end YM.CF.Oath
end
