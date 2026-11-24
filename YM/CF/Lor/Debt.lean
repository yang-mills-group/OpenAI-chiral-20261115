import YM.CF.Lor.Pledge
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable (q:Chi)(j l n:ℕ)
namespace rates
variable (C M X B a:ℝ)(n l j:ℕ)(R:Patch)
-- β expositions GROWTH
local notation "g"=> Scales.g SU.group R.L
local notation "y"=> Scales.y SU.group R.L
local notation "p"=> Scales.p SU.group R.L
local notation "z"=> fun x:ℝ=> B*p x
local notation "s"=> fun x:ℝ=> Cay.burn a x R
local notation "κ"=> Jet.composeCost
-- voucher with explicit (g,v)^j. trim.Z etc afterwards.L's robust 
private def leafB (j n:ℕ)(C M v t w:ℝ):=κ n ((2^n*(w*(v*C)))^j* κ n M t) (1/2)
def billC(v:ℝ)(x:ℝ):= 2*y x * leafB j n C M v 1 (2*g x)
lemma bill_place :sizeK R.L 1 fun x:ℝ=>billC C M n 3 R (z x) x:=by -- order!
 let u:= ((sizeK.scale (sizeK.height R.L) B).tint (sizeK.mild R.L C)); let v:= ((sizeK.main R.L).scale 2); apply year_r; apply arm; exact ((((v.tint u).scale (2^n)).square 3).tint (sizeK.mild _ _)) -- tune
lemma pulseC {x β:ℝ}(v:ℝ)(p1:0 ≤ v)(hp:0<y x)(h:β∈Set.Icc (y x/2) (2*y x))(hh:0 ≤ s x)(hc:s x ≤ 1)(ht:0≤C)(hb:0≤M): |β| * mon3 n j C X M β v (s x) ≤ billC C M n j R v x:=by
 have p2:= (half_pos hp).trans_le h.1; let V:=s x; have hv:0 ≤ V:=hh; have hg:0≤coupling β:= (coupling_pos p2).le
 unfold mon3 billC leafB Jet.composeCost; rw [abs_of_pos p2, abs_of_nonneg hg]; change β * ((n.factorial:ℝ) *( _*((n.factorial:ℝ)*M*(1+V)^n))*_) ≤_
 have hM:=Scales.gauge SU.group R.L hp; gcongr <;> first|exact h.2| exact compare_v G₅ R.L x h hp|>.1| linarith only [hc,hv,show s x=V from rfl]
end rates
open rates
variable{c f:Side}{S:StepData c f}(q:Chi){v x s β D:ℝ}{F:Tube SU.group S}(R:Patch){M: Monk SU.group S}
lemma infant_p(o: Site c)(P: Finset (Along S))(i:Signed): (P.filter fun v=> herald S i v=o).card ≤ about S.patch.L 0:= (card_le_card (show _⊆ Cay.peakM S i o 0 from fun v h=> mem_filter.mpr ⟨mem_univ _, by rw [(mem_filter.mp h).2]; exact (separation_self _).le⟩)).trans (num_peak ..)
lemma trestle(o: Site c): (univ.filter fun i:Bond f=> S.ratio.parent i.1=o).card ≤ Fintype.card Axis * S.patch.L.val^4:=by simpa only [card_singleton,mul_one] using (fine_count (univ.filter fun i:Bond f=> S.ratio.parent i.1=o) {o} (fun i p=> mem_singleton.mpr (mem_filter.mp p).2))
section pay
variable{K:ℝ}{N P B':Side}{S:StepData (Domain N B') (Domain P B')}{G:Ratio (mid N B') (mid P B')}{T:Tube G₅ S}{e:ℝ}(U:Muster G S x e T)(M: Monk SU.group S)
local notation "u"=>Domain N B'
local notation "A"=>Directions SU.group (Domain N B')
local notation "X₀"=>fun y:A=>M.atop y x
local notation "X₁" =>fun y:A=> violet (X₀ y)
local notation "β"=> U.beta
local notation "I"=> U.loft
local notation "q₀"=> U.trot
local notation "l₀"=> U.post
local notation "d₀"=> U.room
local notation "S₀"=> fun i:A=> violet (X₀ i)
local notation "R_" => fun i=> rush x M.key i I
private def Bx(o:Site (Domain N B'))(i:Bond (Domain P B')):=S.ratio.parent i.1=o
def patC (P':Monk SU.group S)(o:Site (Domain N B'))(s:Signed):= ∑ i∈(rush x P'.key s I).filter (fun i=> herald S s i=o), shotB (dense T x q₀ d₀ l₀ β s i) P'
local notation "p'" => about S.patch.L 0
variable{r s a b C D C' M' t w:ℝ}
lemma stemK (o:Site (Domain N B'))(h:Cay.Carbon R x U.beta d₀ r v a b D K C C' M' n l₀ I T M q₀)(hv:0 ≤ v)(hβ:U.beta∈ Set.Icc (y SU.group R.L x/2) (2*y SU.group R.L x))(hx:0<y SU.group R.L x)(hk:0≤M')(hs:0 ≤ Cay.burn a x R)(p:Cay.burn a x R ≤ 1)(hK:0≤K): let P:= fun i=> Lich.Muster.wish U (X₀ i) o; let Q:= fun i=> Lich.Muster.wish U (S₀ i) o; let x' (j):ℝ:=(p':ℝ)*rates.billC K M' n j R v x
 Allows n P 0 (x' 3) ∧ Allows n Q 0 (x' 3) ∧ Allows n (P+Q) 0 (x' 4+x' 4):=by
 intro P Q x'; let Y:=Cay.burn a x R; let T0(j):=mon3 n j K (M'*Y) M' β v Y; have hc:0 ≤ Y:=hs; have hp (j): 0 ≤ T0 j:=by unfold T0 mon3 Jet.composeCost; positivity
 let L(s):=(R_ s).filter fun z=>herald S s z=o
 let X(s: Signed)(i:A):= patC U (X₀ i) o s; let V(s:Signed)(i:A):=patC U (X₁ i) o s
 have he(s:Signed): (Allows n (X s) 0 ((p':ℝ)*T0 3)∧Allows n (V s) 0 ((p':ℝ)*T0 3)∧Allows n (X s+ V s) 0 ((p':ℝ)*(T0 4+T0 4))):=by
    let H(i):=dense T x q₀ d₀ l₀ β s i; let P'(i:Along S)(y:A):=shotB (H i) (X₀ y); let W(i:Along S)(y:A):=shotB (H i) (X₁ y); have hv': (#(L s):ℝ) ≤ p':= Nat.cast_le.mpr (infant_p ..); let u'(i:Along S)(g:i∈ L s):=h.par s i (mem_filter.mp g).1
    refine ⟨(summed (L s) P' (fun i p=> (u' i p).1)).mono (mul_le_mul_of_nonneg_right hv' (hp _)),(summed (L s) W (fun i p=> (u' i p).2.1)).mono (mul_le_mul_of_nonneg_right hv' (hp _)),?_⟩
    apply ((summed (L s) (fun i y=> P' i y+W i y) fun i p=> (u' i p).2.2).mono (mul_le_mul_of_nonneg_right hv' (add_nonneg (hp _) (hp _)))).germ; filter_upwards with i; rw [sum_add_distrib]; rfl
 have hy(j):|β| * T0 j ≤rates.billC K M' n j R v x:=rates.pulseC _ _ _ a _ _ R v hv hx hβ hs p hK hk -- tune order
 have hz(k:ℕ):|β| * ((p':ℝ)*T0 k) ≤ x' k:=by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hy _) (Nat.cast_nonneg _)
 constructor; exact (((allowedAv X _ (fun i=> (he i).1)).smul (-β)).mono (by rw [abs_neg]; exact hz _))
 refine ⟨(((allowedAv V _ (fun i=> (he i).2.1)).smul (-β)).mono (by rw [abs_neg]; exact hz _)),?_⟩; apply (((allowedAv _ _ (fun i=> (he i).2.2)).smul (-β)).mono (by rw [abs_neg,mul_add,mul_add]; exact add_le_add (hz _) (hz _))).germ; filter_upwards with i; change -β*averaged (fun s:Signed=>(X s i+ V s i))=-β*averaged (fun s=> X s i) + -β*averaged (fun s=> V s i); rw [av_add]; ring
end pay
end YM.CF.Lor
