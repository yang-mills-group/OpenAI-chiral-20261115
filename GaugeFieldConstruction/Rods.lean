import GaugeFieldConstruction.Twitter
set_option autoImplicit false
set_option maxHeartbeats 45000
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
local instance localeRodsT (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance localeRodsB (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
open Fock.Flux Girt
local notation "Xq" s:max => hat P.R.L P.x s
variable {J:Type*} [DecidableEq J]
open Guide Fock.Flux
-- Template at all angular orientations and P4 pricing. Bind costs tightly. Proof Lt uses these via actual marks.
def ModelS (s i k:ℕ)(X:Orbit (count Y s i)→ℂ) := (∫ v,X v ∂city _)/ (compensated P.U (gram Y s i k) (room Y s i))
def graphicMode (s i k:ℕ)(A:Pane (count Y s i) → FC (Single (count Y s i))) := ModelS Y s i k (PryF Y s i k A)
lemma twin_p (s i k:ℕ)(A:Pane (count Y s i)→ FC (Single (count Y s i))) : graphicMode Y s i k A= Buffered.Afterglow.Journey.compass Y i k s (fun x=> A x.1) :=by
 let f:= (fun x:Buffered.Fields (count Y s i)=> A x.1); unfold Buffered.Afterglow.Journey.compass; rw [←Buffered.same_ratio]; rfl
local notation "Hk" n:max=> FC (Single n)
-- y counter precision both tested and atlas; v tier price; m max length needed. One per pre-L filing.
structure Gambit (s i k:ℕ)(b:Support (More (count Y s i)))(v e:ℝ)(m:ℕ)(A:Pane (count Y s i) →Hk (count Y s i))(u:ℂ) : Prop where
 full : Upright (count Y s i) b v m A
 target : ‖u‖≤v
 roof : let G:= gram Y s i k; let N:=More (count Y s i); let x:= Xq s
        ∀ (T:Oak Y s i)(t:Signed)(Z:G.path.Bounds G.funds P.K.top.width P.K.top.paths P.V.W.bar)(W:Attached (P.V.L.H (Y.uv k-s)) G.path),
           ∃ F:Altar SU.group N→ℂ, Atlas Z W G.p T.T (clocks.height x) v e G.beta (badgeDust x) (suitCost P.R.L x) (b.image (affine t⁻¹ 0)) (MapΘ Y s i k t A) F ∧ ‖collectionS Z W F-u‖≤ e
lemma Emergence (p:Geometry P)(q:Spicing P)(U:Cash_T P.V P.d P.h)(m:ℕ)(V E:ℝ→ℝ){f e:ℝ}(pf: RunRate 0 f V)(pe:RunRate 0 e E)(hg:∀ᶠ x:ℝ in atTop,0 ≤ V x):
 ∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k → (Y.voyage i).kick ≤ k → ∀ (J:Type _)[DecidableEq J],∀ (A:J→ Pane (count Y s i)→Hk (count Y s i))(u:J→ℂ)(S:J→Support (More (count Y s i)))(q:List J),q.Nodup → Set.PairwiseDisjoint ↑(q.toFinset) S → (∀ j∈q,Gambit Y s i k (S j) (V (Xq s)) (hairFee (Xq s)) m (A j) (u j)) → sites (count Y s i)≤ E (Xq s)*q.length → ∀ z:J→ℂ,(∀ j∈q, ‖z j‖ ≤ KeyTurn (Xq s)) → ‖graphicMode Y s i k (ShootF q z u A)‖ ≤ Real.exp ((KeyTurn (Xq s)*ClockTurn (Xq s)) * q.length):=by
 obtain ⟨C,D,t1,t2,t3,t⟩:= exhib_T Y U (1/8) (by norm_num)
 let F:=P.K.top.clip; let L:=P.R.L; let K:=1+D
 have hk:1 ≤ K:= le_add_of_nonneg_right t2.le; have hv:D ≤ K:=le_add_of_nonneg_left zero_le_one
 have hX: RunRate (-callE/2+0) (0+f) (fun x=> KeyTurn x*((V x*K^m)+V x)):= (RunRate.coins _ _ _).mul ((pf.muc _).add pf)
 let hL:= RunLoose F L (fun x=>KeyTurn x*((V x*K^m)+V x)) hX (by norm_num [gratuity,callE]) (hg.mono fun x H=>by have hv:0 ≤ K^m:=pow_nonneg (zero_le_one.trans hk) _; exact mul_nonneg (BProof.coin_pos ..).le (add_nonneg (mul_nonneg H hv) H)) (1/8) (1/8) (by norm_num) (by norm_num)
 let Yt:= stage_slope P.V P.x
 filter_upwards [pressure_path Y p q,t,houses_P Y,board_grant Y,Yt.eventually_gt_atTop 0,Yt.eventually (wall_matures L),Yt.eventually hg,Yt.eventually hL,Yt.eventually (sailR pf pf pf E pe C K m),seasonal_m Y p q,trees_held Y] with s H G h b w ht tl ξ qL Q tH i k r r' J _ A u S q ℓ ha hA f z e
 let N:=count Y s i; let x:= Xq s; let Z:=KeyTurn x; let Z':=ClockTurn x; let a:=hairFee x; let v:=V x; let pZ:= ℓ; let I:= q.toFinset; have hpV:0≤v:=tl; have heZ:0<Z:=BProof.coin_pos ..
 let X:=gram Y s i k; let T:= (tH i).some; let β:=X.beta; obtain ⟨-,B0,B1,y,-⟩:=prices_plot Y s i k r; -- names tune
 let d:=saveZ x*sites N; let τ:ℝ:= tauTicket F β x; let κ:= boldTicket F β x; let D':= Tor (BeatTurn x) C K Z v m q.length +2*(Crest v v Z K m)^2*q.length
 let χ:=(fun b: ℝ=>b*saveZ x*sites N); let FEE:=(I.card:ℝ)*(Z*(a+a))+d+Regis.trend*(Z*v)^2*I.card
 obtain ⟨Zh,Wp,uP⟩:= (h _ _ r).support
 obtain ⟨hx,χB,πB⟩:=G _ _ r; let w0:= P.dpos
 let A'(j:Signed)(U:Pane N):= ∑ l∈I,(z l*(MapΘ Y s i k j (A l) U-u l)).re
 let Φ:=fun j:Signed=> restrictU X.p ((I.card:ℝ)*(Z*(v+v))) (A' j)
 have hi(j:Signed):Envelope (Φ j):=by
    apply restrictU_h; -- Env.sum template on ALL functions indices? see
    have hp(q':Finset J)(p:q'⊆I): Envelope (fun U:Pane N=> ∑ l∈q',(z l*(MapΘ Y s i k j (A l) U-u l)).re):=by
       induction q' using Finset.induction_on with
       | empty=> simp only [sum_empty]; exact Envelope.const _
       | @insert l q' L H=>
           let Γ(c:ℂ):=(z l*(c-u l)).re; have he : Envelope (fun U:Pane N=> Γ (MapΘ Y s i k j (A l) U)):= Girt.pole_w (MapΘ Y s i k j (A l)) Γ (by unfold Γ; fun_prop) (U_scope Y s i k j (hA l (List.mem_toFinset.mp (p (mem_insert_self ..)))).full); simp_rw [sum_insert L]; exact he.add (H (subset_trans (subset_insert ..) p))
    exact hp I (by exact subset_refl _)
 have he(l:J)(q:l∈ I): Gambit Y s i k (S l) v a m (A l) (u l):= hA l (List.mem_toFinset.mp q)
 have Hp:∀ j,ModerateP Zh Wp X.p T.T (clocks.height x) (badgeDust x) X.beta (suitCost P.R.L x) FEE (τ/8) (κ/8) (Φ j):=by
    intro j; classical
    choose X' hX using fun i u=> (he i u).roof T j Zh Wp; -- eta hX on ∧
    let V'(p:J) (Y:Altar SU.group (More N)):= if h:p∈I then X' p h Y else 0
    have htV(p:J)(h:p∈I): V' p=X' p h:=funext fun Y=> by unfold V'; rw [dif_pos h]
    let B'(p:J):= MapΘ Y s i k j (A p); let S'(i:J):= (S i).image (affine (R:=Per (More N)) j⁻¹ 0) -- shadow indices; change
    let V:=v*K^m; have hf:0≤V:= mul_nonneg hpV (pow_nonneg (zero_le_one.trans hk) _)
    have hl(t)(j':t∈I)(U:Pane N):‖B' t U‖ ≤ V:=by
        let S:= χB (1:Seat N→ SU.E) 0 (by simp); apply (quot_cost _ (actual_f Y s _ k).2 _).trans; exact pulse (token_V hx (by rw [P.kJ]; decide) X.J.M) (baseP hx X.J.M) S.1 S.2 hk hv ((he t j').full.holds _)
    exact ChimeB Zh Wp I S' z heZ.le (fun i x=> e i (List.mem_toFinset.mp x)) hpV V' B' (fun i v=>htV i v ▸ (hX i v).1) (court_sep I S ha j) u a (fun i v=>htV i v ▸ (hX i v).2) V v hl (fun i v=>(he i v).target) hf hpV d (τ/8) (κ/8) (BProof.coin_pos ..).le (BProof.coin_pos ..).le T.oddP (ht T.r.count T.mark) (fun Wa Da=>by
       have ht:= ξ β y.1 T.r T.oddP T.mark Wa Da; unfold d; rw [←sites_as_price]; rw [show τ/8= 1/8*τ by ring,show κ/8=1/8*κ by ring]; exact ht)
 have hβ:0<β:=(half_pos w).trans_le y.1; have hb:0≤ τ:=by unfold τ tauTicket; have h:=F.tail_pos; positivity
 obtain ⟨fZ,pF⟩:= uP T 0 (κ/8) (τ/8) (κ/8) FEE Φ hi (div_nonneg hb (by norm_num)) le_rfl le_rfl le_rfl Hp
 let M(x:Orbit N):= segments X.path X.funds X.p X.beta 0 (κ/8) (badgeDust (Xq s)) (fun j U=> Φ j (tailored T.T U)) x.1
 let X' := PryF Y s i k (ShootF q z u A); let C':=compensated P.U X (room Y s i); let Q':=ØCost Y s i k; let D0:= Real.exp (Z*Z'*q.length);
 let μ:=city N; 
 let R:= D'+(d+1/8*d)
 have hph : ∀ᵐ x ∂μ,‖X' x‖≤ Q'*(Real.exp R * M x):=by
     filter_upwards [actually_ok Y s i k r] with Yv htY
     have hQ:0<Q':=(debit_eq Y s i k).1
     -- divide by Q'
     rw [mul_comm Q', ← div_le_iff₀ hQ]; apply convex_t Y s i k T X.p X.funds β 0 (κ/8) (badgeDust x) R 0 Φ (div_nonneg (norm_nonneg _) hQ.le); intro j
     apply (div_le_iff₀ hQ).2
     have H :‖acts (offWall Y s i k (Loose j T.T Yv.1) 1) (Graph.recX P.U X (room Y s i) Yv)‖ ≤ Graph.past X Yv.1*Real.exp (d+1/8*nativeCost Y s i k Yv):=by
        apply (uses_reg Y s i k Yv) ▸ πB j T Yv 1 (by norm_num) (X.board Yv) _ ?_
        unfold d; rw [←sites_as_price] -- tune
        exact b _ _ r _
     apply (hour_now Y s i k r q z u A S (fun i v=> (hA i v).full) ha hk hv ℓ (show 0<BeatTurn x from BProof.coin_pos ..) hpV (fun i v=> (hA i v).target) hpV heZ.le e t1.le hx qL.1 j T Yv (fun u v=>χB (Loose j T.T Yv.1) u (show |u|≤ 1 from (abs_of_nonneg v.1).le.trans v.2)) _ H).trans
     let X₁:= tailored T.T (pull j 0 Yv.1)
     have hτ:Φ j X₁=A' j X₁:=if_pos (turn_valid N _ Yv.1 j htY _);
     conv_rhs=> rw [mul_comm _ Q',hτ]
     apply mul_le_mul_of_nonneg_left _ hQ.le; unfold Graph.past; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
     have hh:nativeCost Y s i k Yv=d+κ*(misdemean (badgeDust x) Yv.1).card:=by unfold d nativeCost CF.Pannier.Damask.VelvetP.lad_z; rw [sites_as_price] -- only matches lhs if syntactic
     rw [hh]; let B:=X.path.inChannels X.funds X.p β Yv.1; apply le_of_eq; let u':= Tor (BeatTurn x) C K Z v m q.length; let w':=2*(Crest v v Z K m)^2*q.length; let i':ℝ:=(misdemean (badgeDust x) Yv.1).card
     rw [zero_mul,add_zero]; change A' j X₁+u'+w'+(-B+(d+1/8*(d+κ*i')))= -B+κ/8*i'+(u'+w'+(d+1/8*d))+A' j X₁; ring
 have hb':Integrable X' μ:= fired Y r' r _ (Shoot_env q z u S A v m fun i p=> (hA i p).full)
 have hc : 0 < ‖C'‖:= (Real.exp_pos _).trans_le (H i k r' r)
 change ‖(_)/C'‖ ≤ D0; rw [norm_div]; apply (div_le_iff₀ hc).2; apply (norm_integral_le_integral_norm ..).trans
 have hInt:= integral_mono_ae hb'.norm ((fZ.const_mul (Real.exp R)).const_mul Q') hph
 rw [integral_const_mul, integral_const_mul] at hInt
 apply hInt.trans; have hp':0≤Q':=norm_nonneg _; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left pF (Real.exp_pos _).le) hp').trans
 rw [show Q' *_= (Real.exp (R+FEE))*(receipt_P Y s i k * Q') from (by rw [Real.exp_add R FEE]; ring)] -- metas
 have hQ:= Q i k r' r; apply (mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le).trans; rw [← mul_assoc, ←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone
 rw [sites_as_price]
 apply le_trans (b:=planR E V V V C K m x*q.length); swap; · exact mul_le_mul_of_nonneg_right qL.2 (Nat.cast_nonneg _)
 have hh:0≤ saveZ x:=(BProof.coin_pos ..).le; let Z₀:=Tor (BeatTurn x) C K Z v m 1; let P':=2*Crest v v Z K m^2; let A0:=Z*(a+a); let B':=Regis.trend*(Z*v)^2; let n:ℝ:= q.length; have hx: D'= Z₀*n +P'*n:=by unfold D' Z₀ Tor n P'; push_cast; ring
 have ht:d≤ saveZ x*E x*n:=by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left f hh
 have he: FEE=n*A0+d+B'*n:= by unfold FEE; rw [show I.card=q.length from List.toFinset_card_of_nodup ℓ]
 change R+ FEE+ 2*saveZ x*sites N ≤ ((Z₀+P')+(A0+B')+10*saveZ x*E x)*n -- tune
 have hv:0≤d:=mul_nonneg hh (zero_le_one.trans (sites_pos _)); unfold R; rw [he,hx,show 2*saveZ x*sites N=2*d from mul_assoc ..]; nlinarith only [ht,hv]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
