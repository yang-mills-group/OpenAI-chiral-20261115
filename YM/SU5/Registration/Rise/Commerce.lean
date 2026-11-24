import YM.SU5.Registration.Rise.RootLine
import SatinThinRoman
/-!
# Renew long columns. Uses `SatinThinRoman` architecture, but now the cost
must pay exponent linear in length of *already* repeated Mark string,
not buying the heat reserve in the root mesh. Isotropic renewal cannot
be used; there is no uniformly bounded time extent. Include not just the
gap ticket but similar principal long-banner estimates.
-/
set_option maxHeartbeats 450000
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
open ClockBooking
local notation "M"=> Ω f
local notation "Z"=> Ω v
variable (j:Axis)
variable {A V₀ v₀ x b z t D:ℝ} {m w:ℕ}

/-- Expense in the Feast's root units; budget on pressure field not on baffles.
This is sufficient, no requirement that it's the cheapest. Slot fee positive in our use. -/
abbrev tiltBase (P:Preparation) (A:ℝ)(f:ℕ) : ℝ := slotFee P f*Real.exp (8*A+1)
local notation "ε"=>meterC (hat P.R.L P.x f)
local notation "T'"=> rural (RootBook Y i k f).p.B
local notation "W"=>repeatD P ℓ (RootBook Y i k f).p.B
local notation "G"=> plusAgain Δ W
local notation "D'" => tiltBase P A f
local notation "E₀" => Journey.compass Y i k v
variable (H:Real.exp 1≤ P.x)(g:Ferry Y v i k)

lemma rent_L {Q u:ℕ}(h: (More M).val^4 ≤ u*Q)(V:ShelterCost c Y f i k)(he:14*meterC (hat P.R.L P.x f)*(Q:ℝ) ≤ 1):steamRent P A f M (2*u) u ≤ tiltBase P A f^u:=by
 let a := ε; have hz:sites M ≤ (u*Q:ℕ):=by unfold sites; exact_mod_cast h
 have hp:0<slotFee P f:= V.load.health.2.2.1; have hε: 0 ≤ a:=by exact hp.le.trans (V.load.health.2.2.2.1)
 rw [tiltBase,mul_pow]; refine mul_le_mul_of_nonneg_left (show Real.exp _≤ _ from ?_) (pow_nonneg hp.le _)
 rw [←Real.exp_nat_mul]; apply Real.exp_le_exp_of_le; push_cast; change 4*A*(2*u)+14*a*sites M ≤ u*(8*A+1); have he:14*a*Q ≤ 1:=he; push_cast at hz; nlinarith only [mul_le_mul_of_nonneg_left hz hε,mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) u)]

local notation "Bγο"=> (16*P.block.val*w:ℕ)
local notation "A'"=> ((P.R.L.val:ℤ)^(v-f))

-- criterion for two purchases. `X` Mark and l at *different* heights. need only transverses after constructing `l` by long placement. Freeze uses mark bound AGAIN at v, obtained simply from BQueue.
lemma refresh_root_line (p:f ≤ v)(V:ShelterCost c Y f i k)(e:14* ε * (↑((4*(d+G))^3*(2*(16*P.block.val*w)):ℕ):ℝ) ≤1)(credit:d+plusAgain Δ (repeatD P ℓ (RootBook Y i k f).p.B) ≤(M).val)
   (L':List (Site (side Y i f))) (X:Site (side Y i f)→Mark (side Y i v))
   (a: IcePlot Y v i k)(u:D*(16/tiltBase P A f) ≤ (Z).val) (d0:0≤D)
   (gr:GraceA P.block (repeatD P ℓ (RootBook Y i k f).p.B) (rural (RootBook Y i k f).p.B) X (Journey.solder Y i k g.depth v) (highTurn P f v) (reserve P ℓ))
   (xv:∀ l':List (Site M), Envelope (l'.map X).prod)
   (φ:∀ u: Fields (Z), ‖(L'.map X).prod u‖ ≤ D^(4*m))(W0:∀ i:Axis,i≠ j→ cows i (upperRoll L') d)
   (hx:outdoor (rural (RootBook Y i k f).p.B) L')(F:L'.length=4*m)(hw:0<w)(hm:0 < m)(x:2*(Bγο)*m ≤ (M).val)(y:(M).val ≤ 4*(Bγο)*m)
   (z:∀ l':List (Site M), outdoor (rural (RootBook Y i k f).p.B) l' → ‖E₀ (l'.map X).prod‖ ≤ steamRent P A f (side Y i f) (2*l'.length) l'.length):
    ‖E₀ (L'.map X).prod‖≤ (3*D')^(4*m):=by
 let d':= tiltBase P A f; let N:=M; let n:= Z; let W'(l:List (Site N)):= (l.map X).prod; let q:= 4*m
 let w':= (4*(d+G))^3*(2*Bγο)
 let F':= E₀; let Z':= solder Y i k g.depth v
 obtain ⟨k',Θ,U,hQ⟩:= transversal_capacity (Nat.add_pos_right d (show 0 < plusAgain Δ W from plusAgain_pos)) (show 0<Bγο by positivity) x y credit
 let J:=(2^k')^3; have hp:0<J:=by unfold J; positivity
 obtain ⟨Y',u',t,hh,E'⟩:= spun_all gr L' (univ.erase j) hx (fun i e=>W0 i (mem_erase.mp e).1) Θ φ
 rw [card_erase_of_mem (mem_univ j), show (univ:Finset Axis).card=4 from by simp [Axis], show 4-1=3 from rfl] at t hh E'; rw [F] at t
 change Y'.length=J*q at t
 have hd:0<d':= mul_pos V.load.health.2.2.1 (Real.exp_pos _)
 have hu:(More N).val^4 ≤ (J*q)*w':= hQ
 have hz:J*q≤ (More n).val^4 := U.trans (pow_le_pow_left' (Nat.mul_le_mul_right 2 (growingM Y i p)) _)
 have hℕ:q≤ J*q:= Nat.le_mul_of_pos_left q hp
 have he(m':ℕ)(g:m'≤ J*q)(l:List (Site N))(h:∀ u, ‖W' l u‖ ≤ D^m'): ‖F' (W' l)-Z' (W' l)‖≤ d'^m':=(a _ (W' l) _ (xv _) h).trans (hailW Y i hd d0 u (g.trans hz))
 have hv: ‖Z' (W' L')‖ ≤ 2*d'^q:=by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hp.ne').mp (E'.trans ?_)
    rw [mul_pow,←pow_mul,Nat.mul_comm q J]
    apply (norm_le_norm_sub_add _ (F' (W' Y'))).trans
    have hwq: ‖Z' (W' Y')-F' (W' Y')‖≤ d'^(J*q):= (norm_sub_rev ..).trans_le (he _ le_rfl _ (by rw [Nat.mul_comm J q,pow_mul]; exact hh))
    apply (add_le_add hwq ( (z _ u').trans (show _≤ d'^(J*q) from ?_))).trans
    · rw [←two_mul]; exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using (pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) (show 1≤J from hp))) (pow_nonneg hd.le _)
    rw [t]; exact rent_L Y i k hu V e
 refine (norm_le_norm_sub_add _ (Z' (W' L'))).trans ((add_le_add (he _ hℕ L' φ) hv).trans ?_)
 change d'^q+2*d'^q≤(3*d')^q; rw [mul_pow 3 d']; have ht:(3:ℝ) ≤3^q:=by simpa only [pow_one] using (pow_le_pow_right₀ (a:=(3:ℝ)) (by norm_num) (show 1≤q by unfold q; omega))
 linarith only [mul_le_mul_of_nonneg_right ht (pow_nonneg hd.le q)]

-- Glue in Leased line. Use d=0 for transverse budget. Test only on one axis!
local notation "loan"=> (14* ε * (↑((4*(plusAgain P.block (repeatD P ℓ (RootBook Y i k f).p.B)))^3*(2*(16*P.block.val*w)):ℕ):ℝ) ≤1)
include g
open Lifted
lemma long_line_issues (p:f ≤ v)(V:ShelterCost c Y f i k)(e:loan) (credit:G≤ (M).val)
    (U:Site (side Y i f)→ Mark (side Y i v))(a:IcePlot Y v i k)(u:D*(16/tiltBase P A f) ≤ (Z).val) (xv:∀ l':List (Site (side Y i f)), Envelope (l'.map U).prod)
    (s:GraceA P.block W (rural (RootBook Y i k f).p.B) U (Journey.solder Y i k g.depth v) (highTurn P f v) (reserve P ℓ))
    (z:∀ l':List (Site M), outdoor (rural (RootBook Y i k f).p.B) l' → ‖E₀ (l'.map U).prod‖ ≤ steamRent P A f (side Y i f) (2*l'.length) l'.length)
    (o:Cover)(hp:W≤ nodeC o j)(hh:nodeC o j+W ≤ (Bγο:ℤ))
    (X:Buffered.Family (tent Y H))(pT:TestFamily (tent Y H) true X)(pX:Tower.distribute Y H v i X=U (wrap M o))(Xv: Tower.pay X D)
    (hm:0 < m)(hw:0<w)(x:2*(Bγο)*m ≤ (M).val)(y:(M).val ≤ 4*(Bγο)*m)(a₀:ℤ) :
    ‖sharp Y H v i k (banner j (A'*w) (A'*((w:ℤ)*a₀)) m X)‖ ≤ (3*tiltBase P A f)^(4*m):=by
 let S:Packing U j M (A'):= {
    footprint v:= {node v}
    turn u:= (plane j u).mills M
    admissible _ := True
    still _ _ := id
    turns x u:=by change Finset.image _ {node x}={node _}; rw [Finset.image_singleton, Shape.nodex]
    reflects x u:= s.spin j u x 
    }
 let r:= Tower.SlabMark.ruler Δ; have hR: r*w=(↑(Bγο):ℤ):=by unfold r Tower.SlabMark.ruler; push_cast; ring
 have ht:Leased Y H v i S (nodeC o) 0 (repeatD P ℓ (RootBook Y i k f).p.B) X 0 (Tower.SlabMark.ruler P.block*w) [wrap M o] := by
    let o':=wrap M o; let v':=nodeC o
    change Leased _ _ _ _ _ _ _ _ _ _ (r*w) [o']
    refine ⟨⟨fun _ _=> trivial,fun y q u e=>?_,fun x p y q u e=>?_,List.pairwise_singleton ..⟩,by simpa only [List.map_singleton,List.prod_singleton] using pX⟩
    · rw [List.mem_singleton.mp q] at e; rw [show u=node (wrap M o) from mem_singleton.mp e]; refine ⟨nodeC o j,by omega,by omega,?_⟩; rw [node_of,wrap_here]
    rw [List.mem_singleton.mp q] at e; rw [show u=node (wrap M o) from mem_singleton.mp e]; refine ⟨nodeC o x,le_rfl,(by omega),?_⟩; rw [node_of,wrap_here]
 let B:= banner j (A'*w) (A'*((w:ℤ)*a₀)) m X
 obtain ⟨J,q,F⟩:= banner_from_unit Y H v i S w ht m (by change 2*(r*w*m)≤_; rw [hR]; convert (Int.ofNat_le.mpr x) using 1; push_cast; ring) a₀
 have hs:outdoor (rural (RootBook Y i k f).p.B) J:= q.clear.imp (fun {x y} g=> s.gap.trans_le (g _ (mem_singleton_self _) _ (mem_singleton_self _)))
 have he(a:Axis)(z:a≠j): cows a (upperRoll J) 0:= ⟨nodeC o a, fun x p=>by obtain ⟨x,v,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp p); exact q.other a z x v (node x) (mem_singleton_self _)⟩
 have hΦ(x:Fields (Z)): ‖(J.map U).prod x‖≤ D^(4*m):=by
    rw [← q.bill]; exact distribute_pay P Y H v i B (main_bill j _ _ m pT Xv).2 x
 change ‖Journey.compass Y i k v (Tower.distribute Y H v i B)‖ ≤_; rw [show Tower.distribute Y H v i B= _ from q.bill]
 apply refresh_root_line Y i k j g p V (show 14* ε * (↑((4*(0+G))^3*(2*(Bγο)):ℕ):ℝ) ≤1 from by rwa [zero_add]) (by rwa [zero_add]) J U a u (Tower.pay_nonneg Xv) s xv hΦ he hs F hw hm x y z
where
 ship_pay {N M':Side} (h:N=M') (B:Mark N) (d:ℝ)(p:∀ x:Fields N, ‖B x‖≤d)(x:Fields M'): ‖Tower.ship h B x‖ ≤ d:=by subst M'; exact p _
 distribute_pay (c:Preparation){m' :ℕ} (Y':Course c (VolumeCape.Dream.Nimbus m')) (H':Real.exp 1≤c.x) (v i:ℕ)(B:Buffered.Family (tent Y' H')){d:ℝ} (p:Tower.pay B d)(x:Fields (Journey.side Y' i v)): ‖Tower.distribute Y' H' v i B x‖≤d:= ship_pay (terrain ..) _ _ (p _) _
omit g

-- Companion habit to `gap_ticket` and `graceful_clock` for absolute prices.
variable (p:f≤r)(y:r≤v)
def earlyLeaf (U t:ℝ){f v:ℕ}(p:f≤v)(o:Site (side Y i f)): Mark (side Y i v):=(↑t:ℂ) • principal Y i k p U o
local notation "tξ"=> earlyLeaf Y i k b t (p.trans y)
lemma jewel_ticket (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A p y b z t)(l:List (Site (side Y i f)))(h:outdoor (rural (RootBook Y i k f).p.B) l):
 ‖Journey.compass Y i k v (l.map tξ).prod‖≤ steamRent P A f (side Y i f) (2*l.length) l.length:=by
 let α:=Fin l.length; let Z':= List.finRange l.length; let V:= Z'.map Prin; have ht:CasePage V:=by
    unfold V CasePage; rw [List.map_map,show (QuadClock.host ∘ Prin) = _root_.id (α:=α) from rfl,List.map_id]; exact List.nodup_finRange _
 have he:= layout_receipt Y X p y u' l.get (solid_call Y i k l h) V ht; have hv: V.map (menuClock Y i k l.get b z t p y)= l.map tξ:=by
    unfold V; rw [List.map_map,show menuClock Y i k l.get b z t p y ∘ Prin= tξ ∘ l.get from funext fun _=> menu0 ..,←List.map_map,List.map_get_finRange l];
 rw [hv] at he; apply he.trans_eq; congr 1
 · simp [Article,mul_comm]
 simp [V,Z']
include H g
lemma graceful_jewel (p:f≤v)(e:ℕ): GraceA Δ (repeatD P ℓ e) (rural e) (earlyLeaf Y i k b t p) (solder Y i k g.depth v) (highTurn P f v) (reserve P ℓ):=by
 refine ⟨by unfold repeatD; omega, fun i' s x u=> ?_, fun i' s x=>?_,?_⟩
 · exact (band_true Y i k i' _ _ (Nat.le_add_right _ (rural e)) (moving_band Y i _ _ x p u) _).smulM _
 · unfold earlyLeaf principal; rw [heel_swing,route_swing]; exact funext fun _=> (by simp only [reflMark,Pi.smul_apply,theta_smul,Complex.star_def,Complex.conj_ofReal])
 intro a t f' B YQ; let z:= Heat.gaugeShift Δ t; let v':= (highTurn P f v t); have hp:highTurn P f v z= Heat.gaugeShift Δ v':=by unfold v' z highTurn Heat.gaugeShift; ring
 have hx: AtSupport false (band (Ω v) a (Heat.gaugeShift Δ v') (reserve P ℓ)) f':= hp ▸ YQ; rw [show B= _ from hp]; exact tenderD Y H v i k g a v' f' hx
omit H g
lemma jewel_envelope (l:List (Site (side Y i f)))(p:f≤v) : Envelope (l.map (earlyLeaf Y i k b t p)).prod:= (receipt_word (fun i'=> (route_owns Y i k _ b (upRoot Y i p i')).smulM _) l (S:=univ) fun _ _=> subset_univ _).env
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
open YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
#print axioms refresh_root_line
#print axioms long_line_issues
#print axioms jewel_ticket
#print axioms graceful_jewel
#print axioms jewel_envelope
