import YM.SU5.Registration.Affine.HaloBudget
/-!
# Single-stamp support relation, extends Passport to mixtures and derivative stencils
Sponsor requests a genuine op norm estimate (over all characters); compile local
approximations at arbitrary inner heat cuts. Use to prove transfer when replacing one
field, even to unequal stamps. The approximants are made to buy **sharp Eu point**
questions, not covariance claims. Also see `the construction notes` for link to mean.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
structure Commission (P:Spine)(a:Axis)(A:P.Swatch):Prop where
    being : A.Finishes
    threshold : P.ThresholdPrice a A
    all : ∀ x:P.Spectrum0 3, A.WPermit x a

-- displacement only in physical time. strict clock_e
abbrev ticketPlus (t:ℝ≥0)(d:ℝ) : ℝ≥0 := Real.toNNReal (↑t+d)
abbrev ticketMinus (t:ℝ≥0)(d:ℝ) : ℝ≥0 := Real.toNNReal (↑t-d)
lemma two_ticket (t:ℝ≥0)(d:ℝ)(p:|d|<(t:ℝ)):
    0<ticketPlus t d ∧ 0<ticketMinus t d ∧ ((ticketPlus t d):ℝ)=↑t+d ∧ ((ticketMinus t d):ℝ)=↑t-d:=by
  obtain ⟨b,c⟩:= abs_lt.mp p; have hl:0<(t:ℝ)+d:= by linarith
  have hr:0<(t:ℝ)-d:= sub_pos.mpr c; exact ⟨Real.toNNReal_pos.mpr hl, Real.toNNReal_pos.mpr hr,Real.coe_toNNReal _ hl.le,Real.coe_toNNReal _ hr.le⟩
structure Stunt where
  performer:P.Swatch
  wage:ℂ
  jump:ℝ
abbrev Stunt.floor {P:Spine} (A: Set P.Swatch)(t:ℝ≥0)(β:ℝ)(k:P.Stunt):Prop:= k.performer∈A ∧ |k.jump| < β ∧ |k.jump|<(t:ℝ)
abbrev Stunt.toner (k:P.Stunt)(s:ℝ≥0)(i:ℕ):(P.ManyF a (Θ x a)).Op := k.wage • k.performer.Wstage x a (ticketPlus s k.jump) (ticketMinus s k.jump) i

variable (K:Set P.Swatch)(W:P.Swatch)
abbrev VistaSum (l:List P.Stunt)(s:ℝ≥0)(i:ℕ): (P.ManyF a (Θ x a)).Op:= (l.map (fun k=>k.toner P x a s i)).sum
local notation "κ"=> P.Swatch
/-- Read on a slightly shifted center at a time only. Does not use x a.e.; threshold over ALL. -/
def Sponsor : Prop:= ∀ s:ℝ≥0,0<s→ ∀ β ε:ℝ,0<β → 0<ε → ∃ l:List P.Stunt, (∀ k∈l,k.floor K s β) ∧ UpTo atTop (fun i x=> W.Wstage x a s s i) (fun i x=> P.VistaSum x a l s i) ε
lemma Sponsor.extending (u:P.Sponsor a K W){K':Set P.Swatch}(f:K⊆K'): P.Sponsor a K' W:=by intro s t β ε p q; obtain ⟨l,g,h⟩:=u s t β ε p q; exact ⟨l,fun i v=>⟨f (g i v).1,(g i v).2⟩,h⟩
lemma Commissioner.stand (Y:P.ThresholdPrice a W)(g: W.Finishes)(s b c:ℝ≥0)(t:0<s)(u:s ≤ b)(v:s ≤ c) : OnTab atTop (fun i x=> W.Wstage x a b c i):=by
 obtain ⟨C,h,Q⟩:= Y s t; refine ⟨C,h,?_⟩; filter_upwards [Q,(g a).eventually (ge_mem_nhds t)] with i B g x;
 rw [W.Wstage_more x a i g u g v]; exact (P.stoves_price x a _ _ _).trans (B x)
lemma OnBills (l:List P.Stunt)(s:ℝ≥0)(β:ℝ)(z:∀ A∈ K,P.Commission a A)(g:∀ k∈l,k.floor K s β) : OnTab atTop (fun i x=>P.VistaSum x a l s i):=by
 induction l with
 | nil=> exact OnTab.zero
 | cons i l ih=>
    obtain ⟨v,hv,t⟩:=g i (List.Mem.head ..); obtain ⟨ha,hb,h,h'⟩:=two_ticket _ _ t; let w:= i.performer; let C:= z w v; have ht := Commissioner.stand P a w C.threshold C.being _ _ _ (lt_min ha hb) (min_le_left ..) (min_le_right ..)
    exact (ht.scaled (w:=fun (_:ℕ) (_:P.Spectrum0 3)=>i.wage) ⟨‖i.wage‖,norm_nonneg _,Eventually.of_forall fun _ _=>le_rfl⟩).together (ih fun k p=>g k (List.Mem.tail _ p))
lemma Sponsor.threshold (u:P.Sponsor a K W)(k:∀ A∈ K,P.Commission a A) : P.ThresholdPrice a W:=by
 intro s p; obtain ⟨w,l,h⟩:= u s p 1 1 zero_lt_one zero_lt_one; obtain ⟨C,v,e⟩:= P.OnBills a K w s 1 k l; refine ⟨1+C,by linarith,?_⟩; filter_upwards [e,h] with i a₀ b₀ x; let Z:= P.VistaSum x a w s i; let Y:= W.Wstage x a s s i; exact (norm_le_norm_sub_add Y Z).trans (add_le_add ((dist_eq_norm Y Z) ▸ b₀ x) (a₀ x))

/- propagate real positions. -/
def slide (p:Vantage)(s:ℝ):Vantage := Function.update p a (p a+s)
lemma slide_at (p:Vantage)(s:ℝ): slide a p s a=p a+s:= Function.update_self ..
lemma slide_zero (p:Vantage): slide a p 0=p:=by unfold slide; rw [add_zero]; exact Function.update_eq_self ..
lemma slide_else (p:Vantage)(s:ℝ){b:Axis}(hb:b≠a):slide a p s b=p b := Function.update_of_ne hb ..
lemma slide_from (p:Vantage): Continuous (fun s=> slide a p s):=by
 apply continuous_pi; intro i; by_cases p':i=a
 · subst i; simp_rw [slide_at]; fun_prop
 simp_rw [slide_else a _ _ p']; exact continuous_const
lemma slide_to (s:ℝ): Continuous (fun p=> slide a p s):=by
 apply continuous_pi; intro i; by_cases p':i=a
 · subst i; simp_rw [slide_at]; exact (continuous_apply a).add continuous_const
 simp_rw [slide_else a _ _ p']; exact (continuous_apply i)

variable (f g:ℝ)(p:Vantage)(s:ℝ≥0)(i:ℕ)
local notation "ℓ"=> τ (p a-f)
local notation "r"=> τ (g-p a)
-- present the shifted term even when interpolating cuts
lemma sliding_ticket (d:ℝ)(u:|d|<(s:ℝ))(e:(s:ℝ)≤p a-f)(v:(s:ℝ)≤g-p a)(c:(W.fieldA i).allowance P a ≤ ticketPlus s d)(y:(W.fieldA i).allowance P a ≤ ticketMinus s d): W.scoop P x a f g (slide a p d) i=T₀ (ℓ-s)*P.cane x a (W.Wstage x a (ticketPlus s d) (ticketMinus s d) i) p*T₀ (r-s):=by
 obtain ⟨hl,hr,pl,pr⟩:=two_ticket s d u; let p':= slide a p d;
 have hp: p' a=p a+d:= slide_at a p d; let l:= τ (p' a-f); let r':=τ (g-p' a); let V:=ticketPlus s d; let Q:=ticketMinus s d; let X:= W.Wstage x a V Q i
 have hx: (V:ℝ)≤p' a-f:= by unfold V; rw [hp,pl]; linarith only [e]
 have hz: (Q:ℝ)≤g-p' a:= by unfold Q; rw [hp,pr]; linarith only [v]
 have he: V ≤ l:= NNReal.le_toNNReal_of_coe_le hx; have hk: Q≤ r':=NNReal.le_toNNReal_of_coe_le hz
 have HZ: l-V=ℓ-s:= NNReal.eq (by rw [NNReal.coe_sub he,NNReal.coe_sub (NNReal.le_toNNReal_of_coe_le e), show (l:ℝ)=p' a-f from Real.coe_toNNReal _ (V.prop.trans hx),Real.coe_toNNReal _ (s.prop.trans e),hp,show (V:ℝ)=_ from pl]; ring)
 have Hp:r'-Q=r-s:= NNReal.eq (by rw [NNReal.coe_sub hk,NNReal.coe_sub (NNReal.le_toNNReal_of_coe_le v),show (r':ℝ)=g-p' a from Real.coe_toNNReal _ (Q.prop.trans hz),Real.coe_toNNReal _ (s.prop.trans v),hp,show (Q:ℝ)=_ from pr]; ring)
 change W.scoop P x a f g p' i = _; rw [W.scoop_reads P _ _ _ _ _ _ (sub_nonneg.mp (V.prop.trans hx)) (sub_nonneg.mp (Q.prop.trans hz)),P.cane_time,W.Wstage_more x a i c he y hk]; change P.cane x a (T₀ (l-V) * X * T₀ (r'-Q)) p'= _;
 rw [HZ,Hp,P.cane_special x a p' p (fun j h=> slide_else a p _ h)]
-- outer heat contraction & linearity
abbrev heatAnchor (f g:ℝ)(p:Vantage)(s:ℝ≥0)(A:(G).Op):(G).Op := T₀ (τ (p a-f)-s)* P.cane x a A p * T₀ (τ (g-p a)-s) -- `p a` unicode
lemma anchor_distance (A B:(G).Op):dist (P.heatAnchor x a f g p s A) (P.heatAnchor x a f g p s B)≤dist A B:= (P.travel_heat ..).trans (P.cane_distance ..) -- maybe field metavars
lemma anchor_price (l:List P.Stunt)(e:(s:ℝ)≤p a-f)(v:(s:ℝ)≤g-p a) (c:∀ k∈l,|k.jump| < (s:ℝ) ∧ (k.performer.fieldA i).allowance P a≤ticketPlus s k.jump ∧ (k.performer.fieldA i).allowance P a ≤ ticketMinus s k.jump) : P.heatAnchor x a f g p s (P.VistaSum x a l s i) = (l.map (fun k=> k.wage • k.performer.scoop P x a f g (slide a p k.jump) i)).sum:=by
 induction l with
 | nil=> simp only [List.map_nil,List.sum_nil,VistaSum,cane,mul_zero,zero_mul,heatAnchor]
 | cons k l ih=>
    obtain ⟨e1,e2,e3⟩:= c k (List.Mem.head ..)
    rw [List.map_cons,List.sum_cons,← ih fun j h=> c j (List.Mem.tail _ h),P.sliding_ticket x a k.performer f g p s i k.jump e1 e v e2 e3]
    unfold heatAnchor VistaSum Stunt.toner; rw [List.map_cons,List.sum_cons]; unfold cane; rw [mul_add,add_mul,mul_add,add_mul]; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
-- indexing varying pose. over all γ.
abbrev VistaAct (l:List P.Stunt)(f g:ℝ)(p:Vantage)(i:ℕ): (P.ManyF a (Θ x a)).Op:= (l.map (fun k=> k.wage • k.performer.scoop P x a f g (slide a p k.jump) i)).sum
lemma anchor_over (u:(s:ℝ)<p a-f)(v:(s:ℝ)<g-p a)(U:0<s)(l:List P.Stunt)(q:ℕ→Vantage)(p0:Tendsto q atTop (𝓝 p))(σ:ℕ→ℕ)(p1:Tendsto σ atTop atTop)(e:ℝ)(k:UpTo atTop (fun i x=> W.Wstage x a s s i) (fun i x=> P.VistaSum x a l s i) e) (g₁: W.Finishes) (j:∀ k∈l, |k.jump| < (s:ℝ) ∧ k.performer.Finishes) : UpTo atTop (fun i x=>W.scoop P x a f g (q i) (σ i)) (fun i x=>P.VistaAct x a l f g (q i) (σ i)) e:=by
 classical
 let H₁(k:P.Stunt)(i:ℕ): Prop:=|k.jump|<(s:ℝ) ∧ (k.performer.fieldA (σ i)).allowance P a ≤ ticketPlus s k.jump ∧ (k.performer.fieldA (σ i)).allowance P a ≤ ticketMinus s k.jump
 have he:∀ k∈l.toFinset,∀ᶠ i in atTop,H₁ k i:=by
    intro k z; obtain ⟨t,p⟩:=j k (List.mem_toFinset.mp z); obtain ⟨hl,hr,_,_⟩:=two_ticket s k.jump t; filter_upwards [(p a|>.comp p1)|>.eventually (ge_mem_nhds hl),(p a|>.comp p1)|>.eventually (ge_mem_nhds hr)] with i v w; exact ⟨t,v,w⟩
 have hx:= tendsto_pi_nhds.mp p0 a
 filter_upwards [(hx.sub_const f).eventually (le_mem_nhds u),((tendsto_const_nhds (x:=g)).sub hx).eventually (le_mem_nhds v), (g₁ a|>.comp p1)|>.eventually (ge_mem_nhds U),p1.eventually k,(l.toFinset.eventually_all).2 he] with i h u' p k' F x
 have hv: P.heatAnchor x a f g (q i) s (P.VistaSum x a l s (σ i))=P.VistaAct x a l f g (q i) (σ i):=P.anchor_price x a f g (q i) s _ l h u' (fun k e=>F k (List.mem_toFinset.mpr e))
 rw [W.precision P x a f g (q i) (σ i) s p h u',← hv]; exact (P.anchor_distance x a f g (q i) s _ _).trans (k' x)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.anchor_over
#print axioms Spine.Sponsor.threshold
#print axioms Spine.sliding_ticket
