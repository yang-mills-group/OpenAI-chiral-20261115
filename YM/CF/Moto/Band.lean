import YM.CF.Moto.Shank
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.CF.Moto.Plot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η tW z g b c AW B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> LeanV (Single Kx)
open Hove Oath
local notation "QΦ"=> Rock Kx
open Hove Haro Taxi
local notation "θn"=> (mid N B)
variable (U: InkD (mid N B)) (Φ:Scree.Hub (mid N B)) (o:Site (mid N B))(t:Φ.val.1=node o)(P₀:BudgetPoint)(hx:PressB P₀ Φ U v z) (w:1≤v)
variable (A:ℝ)(ht:DayT P₀.order A)(uA:0≤A)
local notation "KP"=> Φrap (mid N B) o 10
local notation "Hq"=> (KP)
local notation "TP"=> plateZ (node o) P₀ (tooth (Φ.val.1) P₀ U)
local notation "TU"=> crest_G P₀ o U
local notation "TΦ"=> crest_Y o U
local notation "QΨ"=> (jetsL o (orbitPH (U 1)))
variable (GG:Oath.Gala P₀.power P₀.order 100 x 3)(hz:1 ≤ radiusB x)(hv: P₀.threshold=temp x)(hK:20 < (More (mid N B)).val)(hk:3 ≤ (mid N B).val)(pK:1 ≤ P₀.power)
local notation "Vcφ"=> deck_K P₀.order P₀.power 10
local notation "Z0"=> crest_G P₀ o U
local notation "Z1"=> crest_Y o U
local notation "T_"=> (Z0+Z1)
local notation "Ψc"=> Taxi.lifeH U 1
-- build pressure.L. at new basis preserving weight4 on halo(++ FIXED). caloric
local notation "PΨ"=> cone_G P₀ o U
local notation "kΛ"=> (Φ.val.2 ∪ (KP).val.2)
local notation "Λξ"=> KP
local notation "ΩΦ"=> Ωbox o Φ 10
open Vow Bake Lilt Larch Rue
-- accumulated finite panel. accepts stated tolerance. choose short projections before expansion. mask price includes post-L blow compensated. Homo.F pledge across Marker.S.T. offsets. only ROOT P Estate local.Captured.
variable {ιZ:Type*}[DecidableEq ιZ]
local notation "Φn"=> (mid N B)
local notation "Gµ"=> (lagE KP)
local notation "Zµ"=> coalesce_zero -- dummy
variable (I:Finset ιZ)(J:ιZ→ Scree.Hub (mid N B))(F:ιZ→InkD (mid N B))(W:ιZ→ℝ)(d₀:ℝ)(u:∀ i∈I,PressB P₀ (J i) (F i) v (W i))(p_:∀ i∈ I,(J i).val.1= node o)(h0:(∑ i∈ I,P₀.mass (J i).val.2 (W i))≤d₀)
variable (l_:ℕ)(hV:10 ≤ P₀.B)
local notation "Ω"=> firth P₀ l_ I J
local notation "Yρ"=> (sunY)
local notation "Bv"=> box_L o P₀ I J l_
local notation "Ev"=> εL o P₀ I J F l_
local notation "Zp"=> Eφ o P₀ I J F l_
local notation "Zv"=> Eκ o P₀ I J F l_
local notation "ZF"=> Z_b (N:=N) (B:=B) o P₀ I J F l_
local notation "qF"=> ℒ_L o P₀ J F
local notation "Z_κ"=> conY o P₀ I J F l_
local notation "TΩ"=> hypeE F (Ω)
local notation "B_W" i:max=> (Ωbox o (J i) 10)
local notation "W'"=> RhoP P₀ A I J W l_
local notation "SW"=> sunY I Bv Ev
local notation "SR"=> (1+ Real.exp P₀.supportExponent * |Kprice P₀ 1 A|)
abbrev seal_R(o:Site (mid N B))(P:BudgetPoint)(F:InkD (mid N B)): Prop:= Taxi.lifeH F 1=0∧ Moto.tooth (node o) P F=0∧ Hove.jetsL o (Haro.orbitPH (F 1))=0
lemma sealer(i:Scree.Hub (mid N B))(U G:InkD (mid N B))(p:seal_R o P₀ U)(u:seal_R o P₀ G)(h w a:ℝ)(hx:PressB P₀ i U h a)(hp:PressB P₀ i G h w)(hu:0 ≤ h): seal_R o P₀ (U+G):=by
 refine ⟨?_,?_,?_⟩
 · change Pastry.pane _=_; rw [Pi.add_apply,hull_sum,show Pastry.pane (U 1)=0 from p.1,show Pastry.pane (G 1)=0 from u.1,zero_add] -- tune unfolds
 · have ht:Moto.tooth (node o) P₀ (U+G)=Moto.tooth (node o) P₀ U+ Moto.tooth (node o) P₀ G:=by
      funext i j; unfold tooth; have hv:Taxi.lifeH (U+G) ∘ increment 1=Taxi.lifeH U ∘ increment 1+Taxi.lifeH G ∘ increment 1:=rfl; change iteratedFDeriv _ _ _ _ _= Moto.tooth _ _ _ i j + Moto.tooth _ _ _ i j; rw [hv,iteratedFDeriv_add_apply (heatP hx hu) (heatP hp hu)]; rfl
   rw [ht,p.2.1,u.2.1,zero_add]
 have h: Haro.orbitPH ((U+G) 1)= Haro.orbitPH (U 1)+ Haro.orbitPH (G 1):=by
    let A:= U 1; let T:= G 1; have ht:= Moto.tail_K (A+T) T; rw [add_sub_cancel_right] at ht; change _= orbitPH A+orbitPH T; rw [ht]; abel -- tune
 rw [h, pub_eq, map_add,←pub_eq,←pub_eq,p.2.2,u.2.2,zero_add]
lemma stillQ : seal_R o P₀ 0:=by
 refine ⟨rfl,?_,?_⟩
 · funext i j; change iteratedFDeriv ℝ 2 (fun _:tangD Φn=>(0:ℂ)) 0 _=0; rw [iteratedFDeriv_const_of_ne (by omega:(2:ℕ)≠0)]; rfl
 rw [show orbitPH ((0:InkD (mid N B)) 1)=0 from ?_,pub_eq,map_zero]; ext i j; rw [orbitPH,Matrix.of_apply,Prism.port_eq]; split; exact rfl; exact mul_zero _
lemma hat_U (i:Scree.Hub (mid N B))(t:∀ j∈I,seal_R o P₀ (F j))(p:∀ j∈I,PressB P₀ i (F j) v (W j))(h:0≤ v):seal_R o P₀ (∑ j∈I,F j):=by
 induction I using Finset.induction with
 | empty=> rw [sum_empty]; exact stillQ ..
 | insert j s k u=>
    rw [sum_insert k]; have ht:= p j (mem_insert_self ..); have hx(x)(z:x∈ s):=p x (mem_insert_of_mem z); have h':= u (fun i p=>t _ (mem_insert_of_mem p)) hx; exact sealer _ _ _ _ _ (t j (mem_insert_self ..)) h' _ _ _ ht (prop_sum s _ _ P₀ v i hx) h
include u p_ GG h0 pK hk hK hz hv hV ht uA w
lemma record_Q: PlotC o l_ P₀ SW v (SR*d₀):=by
 let E:= SW
 obtain ⟨hp,hq⟩:= pitch_s o P₀ w A ht uA GG hz hv hK hk pK I J F W d₀ u p_ h0 l_ hV
 let H:= fun i p=> churn_i o P₀ w A ht uA GG hz hv hK hk pK I J F W d₀ u p_ h0 l_ hV i p; refine ⟨hp,hq,fun i g=>?_⟩
 exact hat_U o P₀ (I.filter (fun j=> Bv j=i)) Ev W' i (fun j v=> (H j (mem_filter.mp v).1).2.2 ((mem_filter.mp v).2 ▸ g)) (fun j v=>(mem_filter.mp v).2 ▸ (H j (mem_filter.mp v).1).1) (zero_le_one.trans w)
-- KUri reallocation earnings post
open Trees
local notation "u'"=> (lagE)
abbrev soy_Z (i: Aura (mid N B)):ℝ:=∑ j∈ Ω,if lagE (Ωbox o (J j) 10)=i then jewelX P₀ A (W j) else 0
local notation "qY"=> soy_Z o P₀ A I J W l_
local notation "θZ"=> (P₀.supportExponent+1+1)
local notation "ΨJ"=> |jewelX P₀ A 1|
local notation "ΨB"=> ΨJ *Real.exp (θZ * (l_+1:ℝ))
lemma bandE: Anuk Z_κ qY P₀ v∧(∀ y:Aura (mid N B), node o∉ y.val → Z_κ y=0) ∧∀ i:Seat (mid N B), tallB qY P₀.B θZ i ≤ ΨB*d₀:=by
 let P:=P₀; let Tp(i:ιZ):= Ωbox o (J i) 10; let L(i):=jewelX P₀ A (W i); let D:= Ω; have hW(i)(p:i∈ D):=jewel_p (F i) (J i) o (p_ i (mem_filter.mp p).1) P₀ (u i (mem_filter.mp p).1) w A ht uA GG hz hv hK hk pK -- need \ D implicit?
 have hY(i)(p:i∈D): 0 ≤ L i := (hW i p ∅).wage (zero_le_one.trans w)
 have hp(i):node o∈(lagE (Tp i)).val:= (Tp i).property
 refine ⟨⟨fun i=>sum_nonneg fun j p=> ?_,fun i u v t=>?_⟩,fun i g=>?_ ,fun i=>?_⟩
 · split; exact hY _ p; exact le_rfl
 · unfold conY ℒ_L; apply Vow.migrate _ _ _ _ v _ _ t; intro i z s _ _; exact hW i z s
 · unfold conY ℒ_L; rw [Finset.sum_apply]; exact sum_eq_zero fun y _=> Pi.single_eq_of_ne (fun (h:i=lagE (Tp y))=>g (h.symm ▸ (hp y))) _
 let V:=ΨJ; let K:=ΨB; have hs:0 ≤ K:= mul_nonneg (abs_nonneg _) (Real.exp_pos _).le; let P':=P₀; let C'(j:ιZ):= P₀.mass (J j).val.2 (W j)
 have hb (i)(p:i∈I) :0≤ W i:=(Taxi.eraF _ _ (u i p) (zero_le_one.trans w) _ (ping_f P₀ ((J i).val.2))).grade
 refine le_trans ?_ (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (s:=D) (filter_subset ..) (f:=C') (fun j p _=> mul_nonneg (Real.exp_pos _).le (hb j p))).trans h0) hs); unfold tallB soy_Z; simp_rw [sum_mul]; rw [sum_comm,mul_sum]; apply sum_le_sum; intro j p; let B0:= lagE (Tp j)
 let R:=univ.filter fun y:Aura (mid N B)=> i∈ y.val; have hp':0 ≤ K*C' j:=mul_nonneg hs (mul_nonneg (Real.exp_pos _).le (hb j (mem_filter.mp p).1)); by_cases hi:i∈ B0.val; swap
 · refine le_trans ?_ hp'; apply le_of_eq; apply sum_eq_zero; intro k s; rw [if_neg (show B0≠k from fun h=>hi (h.symm ▸ (mem_filter.mp s).2)),zero_mul]
 rw [sum_eq_single_of_mem B0 (show B0∈R from (mem_filter.mpr ⟨mem_univ _,hi⟩)),if_pos rfl]; swap; · intro k _ v; rw [if_neg (Ne.symm v),zero_mul]
 have he':coverNumber P₀.B B0.val ≤ l_+1:=by
    have hp:=(μlan o P₀ w A ht uA GG hz hv hK hk pK I J F W d₀ u p_ h0 l_ hV j p).1; have he': (coverNumber P₀.B (J j).val.2)^3 < l_:= (mem_filter.mp p).2; exact hp.trans (Nat.add_le_add_right ((Nat.le_self_pow (by omega) _).trans he'.le) _)
 have he:currency P₀.B θZ B0.val≤ Real.exp (θZ*(l_+1:ℝ)):=Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast he') (add_nonneg (add_nonneg (P₀.exponent_pos.le) zero_le_one) zero_le_one))
 let Z:= W j; have h₁:=hb _ (mem_filter.mp p).1
 have hm:L j≤ ΨJ * W j:=by
    rw [show L j= jewelX P₀ A 1* W j from (by unfold L jewelX trotΦ tera_ρ chipZ chal tollV; ring)]; exact mul_le_mul_of_nonneg_right (le_abs_self _) h₁
 let V1:=C' j; have hz:W j≤ V1:= le_mul_of_one_le_left h₁ (Real.one_le_exp (mul_nonneg P₀.exponent_pos.le (by positivity)))
 change L j*Trees.currency _ _ _≤ _; exact (mul_le_mul (hm.trans (mul_le_mul_of_nonneg_left hz (abs_nonneg _))) he (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (h₁.trans hz))).trans_eq (by unfold V1; ring) -- tune
end YM.CF.Moto
