import SU5SatinMarkedCurrentNovember7
import YM.SU5.LitCurrent.History
import YM.SU5.LitCurrent.Bloom
/-!
# Checkpoint 1 Lit Source purchases

First mark and actual-sector prices (including tails, failures, Reg tilt,
distinct poses on the allocated mesh, paid on same M8 vacuum) and full
per-site projector coefficient passed to **physical mask** on this
stencil. Second fee already Q times NPL. Not a perturbatively assigned
Y.Pay for its nontrivial projector & actual Aim(p), selected path only.
Before derivative-to-integrated Ward comparison estimates across the meshes.
-/

set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace Spine
universe u
-- For fixed finite number Mc of root-types available at each seat,
-- issue the OrbitPulse economics together with Reg.
open Ione Vow
open _root_.Zephyr.Chern LitCurrent
variable (P:Spine)
def jump128 :=8*P.par.block.val
lemma jump_pos : 0<P.jump128:=Nat.mul_pos (by decide) P.par.block.property
-- gauge vs matter coordinate units here: gauge spacing, from I.
def spacing128 (s:ℕ):ℝ:= (2*(P.par.R.L.val:ℝ)^s)⁻¹
lemma meshCurrent(s:ℕ): (P.jump128:ℝ)*(2*P.spacing128 s) = (mill (timeMesh P.par) s:ℝ):=by
 unfold jump128 mill spacing128; simp only [timeMesh,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast, NNReal.coe_ofNat,Nat.cast_mul,Nat.cast_ofNat]
 field_simp

local notation "par0"=> P.par
local notation "Y"=> P.run
private lemma siteClaim (p:_root_.Zephyr.Chern.SprigFee P)(S: Finset Cover) : ∃ c:ℝ,0<c∧∀ᶠ s in atTop,∀ i k:ℕ,∀ x∈S, Stakes (localLevel (funde P.par.K.j (blood Y i k s) (age Y i s)) x) c:=by
 classical
 induction S using Finset.induction_on with
 | empty=> exact ⟨1,zero_lt_one,Eventually.of_forall fun _ _ _ _ u=>by simp at u⟩
 | insert x b u ih=>
    obtain ⟨d,v,q⟩:=p.actual x
    obtain ⟨c,t,e⟩:=ih
    refine ⟨min c d, lt_min t v,?_⟩; filter_upwards [q,e] with s q e i k z l; obtain rfl|g:=mem_insert.mp l
    · let V:= funde P.par.K.j (blood Y i k s) (age Y i s); let A:=Dial.tickA (age Y i s); let U:=StressExchange.houseW (wrap (age Y i s) z); let y:=q i k; obtain ⟨a,b⟩:= y (-(Matrix.trace (A*U)))
      have hp:localLevel V z= (sparSite (N:=age Y i s) P.par.K.j (blood Y i k s) z+Function.const _ (-(Matrix.trace (A*U)))):=funext fun i=> by change localLevel V z i=_root_.Zephyr.Chern.sprig V (_root_.Zephyr.Chern.stream _) z i+_; rw [hike_local,sub_eq_add_neg]; try rfl
      change Stakes (localLevel V z) _; rw [hp]; exact ⟨a,(min_le_right ..).trans b.le⟩
    have hp:=e i k z g; exact ⟨hp.1,(min_le_left ..).trans hp.2⟩

abbrev StampMark (P:Spine)(r s i k:ℕ)(a v:ℝ):=
 LitCurrent.Pattern (funde P.par.K.j (blood P.run i k s) (age P.run i s)) (Moire.bloom (RootBook P.run i k s).J.P) r P.par.d a v
-- keep actual supports visible, BEFORE path cutoff/disclosure limiting outputs
structure UnderLease (r:ℕ)(x:Cover):Prop where
 eventual : ∃ a b v c:ℝ,0 < a∧ 0 < b∧ 0 < v ∧ 0 < c ∧
    (∀ w:ℝ, BPress.NPL (matA P.run r a b v w) ∧ BPress.NPL (matB P.run r a b v w)) ∧
    ∀ᶠ s:ℕ in atTop,∀ i k:ℕ, s<P.run.uv k → let R:=RootBook P.run i k s; let X:= hat P.par.R.L P.par.x s; let d:=R.p.B/10; let loom:=(P.run.voyage i).CapeT s; let m:=age P.run i s
       MaskPoint P.run r s i k a b ∧
       ∃ E:StampMark P r s i k a v, Stakes (compassLine E x loom R.p d) c ∧ ∀ w:ℝ, ∃ M: Site (age P.run i s)→Sour.Bag (age P.run i s),
        (∀ u:Site m, Booked P.run w E u (M u) (matA P.run r a b v w X) (matB P.run r a b v w X * pinpr P.par.R.L X)) ∧
        ∀ L:List (Site (age P.run i s)), L.Pairwise (fun x y=> Disjoint (Preparation.purchased P.run (i:=i) (k:=k) (s:=s) x) (Preparation.purchased P.run (i:=i) (k:=k) (s:=s) y)) → (P.run.voyage i).kick≤k →
        let V:=partitionZ R P.par.U loom; let z(U:Orbit (age P.run i s)):= inner ℂ (Dial.mateK m) (atPilot (i:=i) P.run (s:=s) (k:=k) U (acts ((L.map fun j=>reelSymbol (i:=i) (s:=s) P.run (M j) U).prod) (Cadre.poseL _ (fueled R.p R.K U))))
        FullBill.Priced P.par.V R P.par.U loom (Preparation.Course.charge P.run s) (P.run.debt s) ∧ V≠0 ∧ Integrable z (city (age P.run i s))∧ markedRead (L.map (cloth P.run w E)).prod loom (denZ R P.par.U loom)/V=(∫ u,z u∂city (age P.run i s)) / V
lemma scheduleLease (pc:P.Roster)(p:_root_.Zephyr.Chern.SprigFee P)(t:Solstitial P.par)(u: RateStamp P.run)(r:ℕ)(h:0<r)(x:Cover): UnderLease P r x:=by
 obtain ⟨a,b,ha,hb,v⟩:= leaseFrame Y pc.prepared u t r
 obtain ⟨W,wv,g⟩:= plan_code r ha hb P.par.d
 obtain ⟨D,⟨z⟩⟩:=oily ha P.par.dpos (breadth x)
 let Z:= layout r x StressExchange.arcOrder
 obtain ⟨c,hc,hf⟩:=P.siteClaim p Z.toFinset
 let L : ℝ:=(Z.length:ℝ)*c; have hp: 0 < L:=mul_pos (Nat.cast_pos.mpr (List.length_pos_iff.mpr (layout_nonempty r h x _))) hc
 constructor; refine ⟨a,b,W,L/2,ha,hb,wv,half_pos hp,fun w=>Preparation.prices P.par.R.L _ _ _ _ _ _ _ ha,?_⟩
 have hm:Tendsto (fun x:ℝ=>Real.exp (-a*((Pressure.radiusB x/10:ℕ):ℝ))) atTop (𝓝 0):=by
    have tD:Tendsto (fun x:ℕ=> x/10) atTop atTop:= tendsto_atTop.mpr fun b=> (eventually_ge_atTop (10*b)).mono (fun i h=>by omega)
    have ht: Tendsto (fun x:ℝ=>(↑(Pressure.radiusB x/10):ℝ)) atTop atTop:= (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tD.comp Work.E01.radiusB_tendsto)
    simpa [Function.comp_apply,Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop ha))
 have ht:Tendsto (fun s=>D*(Real.exp (-a*((Pressure.radiusB (hat P.par.R.L P.par.x s)/10:ℕ):ℝ))*expiry (4*a) W)) atTop (𝓝 0):=by simpa only [mul_zero,zero_mul,Function.comp_apply] using (((hm.comp (turnover P.par)).mul_const (expiry (4*a) W)).const_mul D)
 filter_upwards [v,hf,ht.eventually (ge_mem_nhds (show 0<L/2 by positivity)),(turnover P.par).eventually (draft_π P.par.R.L)] with s p g0 ht hf i k yK; intro R X d K m
 let S:=funde P.par.K.j R.J.M (age Y i s); let T:=Moire.bloom R.J.P; let A:= StampMark P r s i k a W
 let P':= p i k yK; obtain ⟨E⟩:=g S T P'.ppm P'.term P'.permit
 obtain ⟨ζ,s₁,s₂,s₃,s₄⟩:=hf; have hx:0<pinpr P.par.R.L X:=s₄.symm ▸ pow_pos s₁ 2
 refine ⟨P',E,?_ ,fun w=>?_⟩
 · have hw:= maskedReward E x P'.C z (fun j t=>g0 i k j (List.mem_toFinset.mpr t))
   refine ⟨hw.1,le_trans ?_ hw.2⟩
   change L/2≤ L- D*(Real.exp (-a*↑(((RootBook Y i k s).p.B)/10)) *expiry (4*a) W); rw [P'.B0]; linarith only [ht]
 choose V H using fun x:Site (age Y i s)=> allBooked Y w P' E x hx
 exact ⟨V,H,fun l h t=>signedPrice Y w E V (matA Y r a b W w X) _ H l h t yK⟩

-- Joint vote. Preserve even period grant and Omni for frames; cannot query
-- this on an unrelated supplied Spine.
structure LitFuture (Mc:ℕ): Prop where
    months:8∣ P.par.M.val
    roster: P.Roster
    season:Solstitial P.par
    rate:RateStamp P.run
    registry:Post124 P.run
    payment:_root_.Zephyr.Chern.SprigFee P
    support: ∃ (Pay x G:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ), Sweepcraft P.run Tξ Pay x G n Mc
    heater: Heater P.par P.run -- optional

lemma tandem(Mc:ℕ):∃ (P:Spine)(K:P.Register), LitFuture P Mc ∧
    ∀ (G:P.Spectrum0 3→Prop), (∀ᵐ x ∂P.pillars 3,G x)→ ∃ x,G x ∧ JointTuple.{u} P K x:=by
  obtain ⟨n,h⟩:= exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
  have hz:0 ≤ strive_E 6:=by
      unfold strive_E Jet.composeCost; positivity
  obtain ⟨P,K,q,r,H,⟨T,t⟩,_,_,hv,hy,_,⟨C,_,_,p⟩,a,k⟩:=
    bookedS n (le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ) ≤ 2+Mc) hz) h.le) (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m⟩:= T.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  have hM:= RateCover.includes _ _ _ m; have even : Even P.par.K.j:= by rw [P.par.kJ]; exact ⟨2,rfl⟩
  exact ⟨P,K, ⟨hy,r,t,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,Preparation.postpaid P.run hM r.prepared,_root_.Zephyr.Chern.SprigFee.paid P,
    ⟨Pay,kC,Γ,Tξ,n,bandRadius P.run (hM.staysOn even P.par.kJ.ge u v Z s p1 p2 Mc ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared⟩, warmDust P.run (hM.fuels even P.par.kJ.ge u v Z s p1 p2) r.prepared⟩,
    fun G g=> reside.{u} P K q r H ht k p G g⟩

theorem candles (Mc:ℕ):∃ (P:Spine)(K:P.Register)(x:P.Spectrum0 3), JointTuple.{u} P K x ∧ LitFuture P Mc ∧ P.UnderLease P.jump128 0:=by
 obtain ⟨P,K,p,t⟩:=tandem.{u} Mc
 obtain ⟨x,_,u⟩:= t (fun _=>True) (Eventually.of_forall fun _=>trivial)
 exact ⟨P,K,x,u,p,P.scheduleLease p.roster p.payment p.season p.rate _ P.jump_pos 0⟩
end Spine
#check @Spine.candles
#print axioms Spine.candles
#print axioms LitCurrent.physical_spelling
#print axioms Spine.meshCurrent -- fix
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
