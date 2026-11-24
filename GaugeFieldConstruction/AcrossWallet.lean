import GaugeFieldConstruction.AcrossCashier
import GaugeFieldConstruction.AcrossL1
import GaugeFieldConstruction.AcrossRouting
import YM.CF.Buffered.DonorGram
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Altitude Tapestry.Exhibition
open TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
-- Real tape. No fictive state.Price calculation may advance by paid shifted Beta–Wave operation to the very same bare-Cap and retains its meaning. Estimate registered paycheck *even* at intermediate.T.
open Heat Buffered Dial Tapestry.Fashion Py.Rate.Branch
variable (R:P.Register){ε:ℕ→ℝ}(E:IntervalsSchedule P n v ε)
local notation "M" => P.par
local notation "Kβ" i:max => (P.run.headIn i)
local notation "ℓσ" i:max s:max=> Journey.side Y i s
local notation "X☆" i:max k:max=> ((Y).voyage i).X ((Y).uv k)
local notation "Cℓ" i:max s:max=> ((Y).voyage i).CapeT s
local notation "Μλ" i:max k:max=> Actual (Y).meter ((Y).voyage i).funds ((Y).voyage i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) ((Y).uv k)
open AcrossShots Tapestry.Ward LocalLimit
abbrev WalletDebtSt (i k:ℕ) (t:ℝ)(r:Bet ((Y).uv k)):Prop:= EarnTrunkSt (P:=P.par.P) (J:=P.par.J) (h:=(Γ).h) (D:=(Γ).δ) (C:=(Γ).C) (R0:=(Γ).R0) (q:=Chi.canonical) (X:=((Y).voyage i).CapeT) (f:=Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) ((Y).voyage i).funds ((X☆ i k).gram) ((X☆ i k).wave) t (v ((Y).uv k)) (ε ((Y).uv k)/(1+totalTickets P i k ((Y).uv k))) r
abbrev priceHere (u:P.Effect)(i k:ℕ)(r:Bet (P.run.uv k))(s:ℕ):ℂ:= markedRead (attire (breathing Y B s i k u)) ((P.run.voyage i).CapeT s) (denZ ((Μλ i k).gram P.par.P r s) (Γ).U ((P.run.voyage i).CapeT s)) / partitionZ ((Μλ i k).gram P.par.P r s) (Γ).U ((P.run.voyage i).CapeT s)

variable {r:Bet (P.run.uv k)}{t:ℝ}
include E
lemma observingSt (w:ReserveTape (P:=P) n i k)(p:WalletDebtSt P v (ε:=ε) i k t r)(s:ℕ)(z:s ≤ P.run.uv k)(A:P.Effect)(H:BillOfWork)(b:ℝ)(e:Pocket P.calibration H s b A): ‖priceHere P A i k r s-taking P.run P.large i k A‖ ≤ ε (P.run.uv k) * (cloudSpan s H*b) :=by
 let K:= X☆ i k
 let l:= Cℓ i s; let f:= breathing Y B s i k A; let g:= (Y).voyage i; rw [taking_phys _ _ _ _ _ _ ⟨w.2,z⟩ e.funded]; change ‖markedRead (attire f) l _ / _ - markedRead (attire f) l (denZ (K.gram s) (Γ).U l) / _‖ ≤ _
 let T:= totalTickets P i k s; let U:= ℓσ i s
 have hp:= p.trueMark.2.2.2.2 s z; let b':= cloudSpan s H*b; have hu:= (p.owes s z).1
 refine le_trans (apply_stable (Γ).U l ((P.run.voyage i).ownership s).paid.bill _ _ (Env.integrableX hp.2.1 (city U)) (Marks.can_read (Γ).V _ _ _ ((Y).each_level i k s w.2 z)) (attire f) (Tapestry.Ward.signs f).env (T*b') (?_) _ hu) ?_
 · intro V; unfold b'; rw [←mul_assoc]; exact le_trans (Ward.pay f _) (P.cardBoundSt H s b A e i k)
 have hT: 1≤ totalTickets P i k s:=P.tickets_hi ..; have hp'T: T ≤ totalTickets P i k ((Y).uv k):= P.totalMono i k z
 have hb:0 ≤ b':= mul_nonneg (cloudSpan_pos s H) e.priced
 let q:= totalTickets P i k (P.run.uv k); let x:= ε ((Y).uv k); have hv:x≥0:=(E.pay _).1.le; have he:0<1+q:=by linarith only [hp'T,hT]
 change T*b'*(x/(1+q)) ≤ x*b'; field_simp; nlinarith only [mul_le_mul_of_nonneg_right (show T≤1+q from hp'T.trans (le_add_of_nonneg_left zero_le_one)) (show 0≤ x*b' from mul_nonneg hv hb)]
lemma hearingSt (W:P.shoulderTape n ε v i k)(p:WalletDebtSt P v (ε:=ε) i k t r)(s:ℕ)(z:s ≤ P.run.uv k)(A:P.Effect)(H:BillOfWork)(b:ℝ)(e:Pocket P.calibration H s b A): ‖priceHere P A i k r s-torqueBare P v A i k‖ ≤ 2*ε (P.run.uv k) * (cloudSpan s H*b) := by
 refine (norm_sub_le_norm_sub_add_norm_sub _ (taking Y B i k A) _).trans ?_; rw [norm_sub_rev (taking Y B i k A)]; linarith [P.uniformMargin v E A e.funded H b e _ _ W z,P.observingSt v E W.1 p s z A H b e]

local notation "xF"=> Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)
local notation "χ"=> ((Y).voyage i)
local notation "ϑ"=> Μλ i k
local notation "ℓ" => P.run.uv k
-- grants ACTUAL; no re-tag mask, no other P.Price. Key qualifier ``Body.raw tariff'' still on Y for lower label definitions; exact step identity gives option to actually advance any SUCH single ticket with the Perturbed Wave/β from there.
omit E
lemma belongsSt (_w: ReserveTape (P:=P) n i k)(p:WalletDebtSt P v (ε:=ε) i k t r) : Granted P.par.U ((Actual (Y).meter (P.run.voyage i).funds ((Y).voyage i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) ((Y).uv k)).gram (Γ).P r) ((Y).voyage i).CapeT Chi.canonical (Γ).J.d ((Y).uv k) ((Actual (Y).meter ((Y).voyage i).funds ((Y).voyage i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) ((Y).uv k)).wave (Γ).P r) (steps (Γ).V (P.run.ir i) (Γ).block (P.run.uv k)) (Γ).R.J:=by
 exact paidStepsSt _ P.par.H (((Y).voyage i).paths ℓ).paid r p.debt
lemma raisedReadingSt (w:ReserveTape (P:=P) n i k)(p:WalletDebtSt P v (ε:=ε) i k t r)(s:ℕ)(z:s < P.run.uv k)(S:Finset Cover)(A:Mark (Journey.side Y i s))(e:AtSupport false (Satin.region S (Journey.side Y i s)) A) :
 let Z:= (Μλ i k).gram (Γ).P r; let C:= ((Y).voyage i).CapeT
 let T:= nextMark (j:=(Γ).K.j) (ho:=(Γ).R.odd_side) Z C Chi.canonical (Γ).J.d ((Μλ i k).wave (Γ).P r) (steps (Γ).V (P.run.ir i) (Γ).block (P.run.uv k)) s A
 AtSupport false (Satin.region (followBox (Λ:=Γ) (l:=P.width) S) (Journey.side Y i (s+1))) T ∧ markedRead T (C (s+1)) (denZ (Z (s+1)) (Γ).U (C (s+1)))/partitionZ (Z (s+1)) (Γ).U (C (s+1)) = markedRead A (C s) (denZ (Z s) (Γ).U (C s))/partitionZ (Z s) (Γ).U (C s) :=by
 intro Z C' Tb
 let P':= P.belongsSt v w p; obtain ⟨u⟩:=P'.grant s z
 obtain ⟨_,_,_,U,_⟩:=u.cap
 have q:(patternA Y s i k).patch.J= (Γ).R.J:= P'.radius _ z
 let Wb:=(Μλ i k).wave (Γ).P r
 let G:=Vale.apt ((Y).ir i) (Γ).block (Γ).R.L s
 have hu:= surround G (patternA Y s i k) (Γ).K.j (Wb s).val (Z (s+1)).J.M (Γ).R.odd_side Chi.canonical (Γ).J.d (Z (s+1)).beta ((C' s)) (Journey.legal Γ) U.bill (P'.branch _ z) u.legal.1 u.legal.2 _ e (Journey.tissue Y i s) (P'.aligned _ z); rw [q] at hu
 refine ⟨ hu.mono (next_contains S _ _ G), ?_ ⟩
 have hv: markedRead A (C' s) (denZ (Z s) (Γ).U (C' s))=markedRead Tb (C' (s+1)) (denZ (Z (s+1)) (Γ).U (C' (s+1))):= single_num (Γ).U _ _ _ _ _ _ _ (Journey.legal Γ) P' (e.mono (Finset.subset_univ _)) z
 rw [hv, show partitionZ (Z s) (Γ).U (C' s)=_ from (p.trueMark.2.2.2.2 _ z.le).2.2.1,show partitionZ (Z (s+1)) (Γ).U (C' (s+1))= _ from (p.trueMark.2.2.2.2 _ z).2.2.1]
variable (r)
abbrev lobbyTape (k:ℕ)(r:Bet (P.run.uv k)):= (Μλ i k).gram (Γ).P r
abbrev climbTape (s:ℕ)(r:Bet (P.run.uv k))(A:Mark (Journey.side Y i s)) := nextMark (j:=(Γ).K.j) (ho:=(Γ).R.odd_side) (lobbyTape (i:=i) P k r) ((Y).voyage i).CapeT Chi.canonical (Γ).J.d ((Μλ i k).wave (Γ).P r) (steps (Γ).V (P.run.ir i) (Γ).block (P.run.uv k)) s A
abbrev carryCostSt (s:ℕ)(A:Mark (Journey.side Y i s)) : ℂ:= markedRead A (Cℓ i s) (denZ ((lobbyTape (i:=i) P k r) s) (Γ).U (Cℓ i s)) / partitionZ (((Μλ i k).gram P.par.P r) s) (Γ).U (Cℓ i s)
-- stating family with casts.Power.F. at EVERY index & neighborhood. constructive survivor statement. Not claiming rerun all thermal lower-bill definitions.
structure PromptsTape (A:Mark (Journey.side Y i s))(S:Finset Cover)(F:∀ j:ℕ,Mark (Journey.side Y i j))(U:ℕ→Finset Cover):Prop where
 origin : F s=A ∧ U s=S
 grows (j:ℕ)(hj:s≤j)(v:j<P.run.uv k) : U (j+1)= followBox (Λ:=Γ) (l:=P.width) (U j) ∧ F (j+1)=P.climbTape j r (F j)
 owned (j:ℕ)(hj:s≤j)(v:j≤(Y).uv k): AtSupport false (Satin.region (U j) (side Y i j)) (F j) ∧ P.carryCostSt r j (F j)= P.carryCostSt r s A
lemma promptingSTELLA (w:ReserveTape (P:=P) n i k)(p:WalletDebtSt P v (ε:=ε) i k t r)(_z:s ≤ P.run.uv k)(S:Finset Cover)(A:Mark (Journey.side Y i s))(e:AtSupport false (Satin.region S (Journey.side Y i s)) A): ∃ F U, PromptsTape P r A S F U:=by
 let G(j:ℕ): Mark (Journey.side Y i j):=Nat.rec (motive:=fun j=> Mark (Journey.side Y i j)) (if h:s=0 then cast (congrArg (fun s=> Mark (Journey.side Y i s)) h) A else 0) (fun j X=> if h:s=j+1 then cast (congrArg (fun s=> Mark (Journey.side Y i s)) h) A else climbTape P (i:=i) j r X) j
 let H:= followBox (Λ:=Γ) (l:=P.width); let U(j:ℕ):= H^[j-s] S
 have h0:G s=A:=by -- dependent s appears A. H definitional. cases.
    cases s with
    | zero=> simp [G]
    | succ i=> simp [G]
 have u0:U s=S:=by rw [show U s= H^[s-s] S from rfl,Nat.sub_self]; rfl
 have hg(j)(t:s≤j): U (j+1)=H (U j)∧G (j+1)=P.climbTape j r (G j):=⟨by unfold U; rw [Nat.succ_sub t,iterate_succ_apply'],dif_neg (by omega)⟩
 refine ⟨G,U,⟨h0,u0⟩,fun i u _=>hg i u,fun j h v' =>?_⟩
 induction j,h using Nat.le_induction with
 | base=> rw [u0,h0]; exact ⟨e,rfl⟩
 | succ j h ih=>
    obtain ⟨t₁,h₁⟩:= ih (Nat.le_trans (by omega : j ≤ j+1) v')
    have hp:= raisedReadingSt P v w p j v' (U j) (G j) t₁
    rw [(hg j h).1,(hg j h).2]; exact ⟨hp.1,hp.2.trans h₁⟩
lemma names_at_tape (w:ReserveTape (P:=P) n i k)(p:WalletDebtSt P v (ε:=ε) i k t r)(z:s ≤ P.run.uv k)(S:Finset Cover)(A:Mark (Journey.side Y i s))(e:AtSupport false (Satin.region S (Journey.side Y i s)) A) : ∃ F U, PromptsTape P r A S F U ∧ let T:Mark (side Y i ((Y).uv k)):= F ((Y).uv k); let a(v:Pane (side Y i ((Y).uv k))):=T (v,v); Envelope a ∧ carryCostSt (i:=i) P r s A=AcrossLands.position (mesh ((Y).ir i) (Γ).R.L ((Y).uv k)) (Γ).U ((Y).meter.a ((Y).uv k)) (v ((Y).uv k)) a:=by
 obtain ⟨F,U,x⟩:= P.promptingSTELLA v r w p z S A e; refine ⟨F,U,x,?_⟩
 intro T a; let l:= Cℓ i ℓ; let μ:= mesh ((Y).ir i) (Γ).R.L ℓ; let D:=(lobbyTape P k r (i:=i)) ℓ
 obtain ⟨hx,ht⟩:= x.owned ℓ z le_rfl; refine ⟨Env.along (g:=fun x:Pane (side Y i ℓ)=>(x,x)) hx.env (measurable_id.prodMk measurable_id),?_⟩
 rw [← ht]; have h:denZ D (Γ).U l= sharpHat μ (Γ).U ((Y).meter.a ℓ) (v ℓ):= p.trueMark.2.2.2.1
 change markedRead T l (denZ D _ l) / partitionZ D _ l= _; rw [markedRead, partitionZ,h]; unfold AcrossLands.position; congr 1; apply integral_congr_ae; filter_upwards with xT; by_cases q:flags ((Y).meter.a ℓ).threshold xT.1=∅
 · let Po := (Y).history i k; have hx:l xT=xT.1:= Vale.Grace.Robes.solar xT l (Po.roof ℓ).paid ((Y).meter.a ℓ) (Po.pole ℓ) q; rw[hx]; rfl
 let C':= sharpHat μ (Γ).U ((Y).meter.a ℓ) (v ℓ) xT; change letterRead (T (drawn l xT)) C'= inner ℂ _ (acts (a xT.1) C'); rw [show C'=0 from Set.indicator_of_notMem (show xT.1∉{v:Pane (side Y i ℓ)|flags ((Y).meter.a ℓ).threshold v=∅} from q) _,map_zero,map_zero,inner_zero_right]
#print axioms names_at_tape
#print axioms hearingSt
#print axioms raisedReadingSt
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
