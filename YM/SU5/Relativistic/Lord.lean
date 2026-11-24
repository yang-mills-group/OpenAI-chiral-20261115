import YM.SU5.Relativistic.Lodges
import YM.SU5.Relativistic.Demi
import YM.SectorNext.VACUUM_NORMALIZATION.Link
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots Precision RG Work.F03
open Next.SectorChange
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable (G : Gauge){W : Side}
local notation "X"=> Config G W
local notation "H"=> Face (Per W)
local notation "ι"=> livelies W
local notation "F"=> Lo W
local notation "Y"=> F→ G.El
open GaugeFlux Pageant
open SectorNext.Vacuum Metric
open scoped Classical
-- W tile
local notation "δ"=> Fintype.card (Fresco G W)
local notation "Z"=> Prices G (Lo W)
def fee (W:Side)(β:ℝ)(u:ChartRatio G)(σ n:ℝ):= spare u β ^ Fintype.card (Lo W) * (Real.sqrt (σ^(Fintype.card (Fresco G W))*n))⁻¹ -- W notation clash?
variable (p:Clip) {σ C Λ:ℝ} (a:ChartRatio G) (D:ℕ)

lemma toll_raw (g:ℝ)(hg:0<g)(u: Y) (t:ℝ) (R:ℝ)(p:0≤t)(f:((limit W:ℕ)*t)^2/2 < R)(v:∀ y:G.El,y∉G.lieExp '' closedBall 0 g→R ≤ G.price y)(k:layOut G u∈ Mild W G t) : let B:Set (F→G.Color):=Set.univ.pi (fun _=>closedBall 0 g); u∈ (release (1:Y) '' B):=by
 intro A
 have hp (i:F) : ∃ x:G.Color,x∈ closedBall 0 g∧ G.lieExp x= u i:=by
    by_contra w; have he:=v _ w; have hx := pow_le_pow_left₀ (G.chord_nonneg _) (lengthsF G u p k i) 2; rw [G.chord_price] at hx; linarith
 choose x h t using hp; refine ⟨x,fun i _=>h i,funext fun i=>?_⟩; unfold release; simp [t]

def chamber (W:Side) (d:ℝ): Set (Lo W→ G.Color):= Set.univ.pi fun _=>closedBall 0 d
def wealthy (x:ℝ)(V:PathData G)(η:ℝ)(z:Y):= Real.exp (-(η*x)*boxE G V D p (layOut G z)/2)
def hostP (d x:ℝ)(V:PathData G)(η:ℝ)(z:Z):= (chamber G W d).indicator (fun y=> pay a y * wealthy G p D x V η (release 1 y)) (tape (coupling x • z))
variable (hy:LocalRatio a)
include hy
lemma halo_transport(d x:ℝ)(v:0<d)(hd:d<a.radius)(hx:0<x)(V:PathData G)(η t R:ℝ)(h:V.Bounds p σ C Λ)(s:0≤t)(f:((limit W:ℕ)*t)^2/2 < R)(u:∀ y:G.El,y∉G.lieExp '' closedBall 0 d→ R ≤ G.price y)(w:0<η) :
    (Real.sqrt x)^δ * (∫ z : X,localPay G V D p t (η*x) z∂prior G W) ≤ ∫ z:Z,hostP G p a D d x V η z:=by
 rw [local_tariff G V D h]; let A:= chamber G W d; let C:= release (1:Y) '' A; let F' :=fun z:Y=> localPay G V D p t (η*x) (layOut G z); let Wf:= wealthy G p D x V η (W:=W); let T:= C.indicator Wf
 have hg:Continuous Wf:=by have h0:= box_c G V D h (W:=W); have ht:= lay_c G (W:=W); unfold Wf wealthy; fun_prop
 have he (z:Y): 0<Wf z:=Real.exp_pos _
 have ht:IsCompact A:= isCompact_univ_pi (fun _=> ProperSpace.isCompact_closedBall ..)
 have hQ: MeasurableSet C:= (ht.image (release_continuous _)).measurableSet
 have hT: Integrable T (piHaar G F):= (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace Wf)).indicator hQ
 have hW(z:Y):0 ≤ F' z∧F' z≤ T z:=by
    unfold F' localPay; by_cases h:layOut G z∈ Mild W G t
    · rw [Set.indicator_of_mem h]; unfold T; rw [Set.indicator_of_mem (show z∈C from toll_raw G d v z t R s f u h)]; exact ⟨(he z).le,le_rfl⟩
    rw [Set.indicator_of_notMem h]; refine ⟨le_rfl,?_⟩; unfold T; by_cases g:z∈C; · rw [Set.indicator_of_mem g]; exact (he _).le
    rw [Set.indicator_of_notMem g]
 have hv: Integrable F' (piHaar G F):= hT.mono' (((local_meas G V D h t _).comp (lay_c G).measurable).aestronglyMeasurable) (Eventually.of_forall fun i=> by rw [Real.norm_of_nonneg (hW i).1]; exact (hW i).2)
 change (Real.sqrt x)^δ * (∫ z,F' z∂piHaar G F)≤_ -- tune
 refine (mul_le_mul_of_nonneg_left (integral_mono hv hT fun z=>(hW z).2) (by positivity : 0≤(Real.sqrt x)^δ)).trans_eq ?_
 let Z':= A.indicator (fun y=> pay a y*Wf (release (1:Y) y))
 have hj:A⊆Next.SectorChange.mouth a:=fun i v x z=> closedBall_subset_ball hd (v x z)
 obtain ⟨-,hp⟩:= release_integral hy (1:Y) T (hg.measurable.indicator hQ|>.stronglyMeasurable) (fun y h=> Set.indicator_of_notMem (fun v=>h ((release_image a (1:Y)) ▸ (Set.image_mono hj v))) _)
 have hy': (Next.SectorChange.mouth a).indicator (fun y=>pay a y • T (release (1:Y) y))=Z':=by
    funext y; unfold Z'; by_cases v:y∈A; · rw [Set.indicator_of_mem (hj v),Set.indicator_of_mem v]; unfold T; rw [Set.indicator_of_mem (show release (1:Y) y∈ C from ⟨_,v,rfl⟩),smul_eq_mul]
    rw [Set.indicator_of_notMem v]; by_cases h:y∈Next.SectorChange.mouth a; swap; · exact Set.indicator_of_notMem h _
    rw [Set.indicator_of_mem h]; unfold T; rw [Set.indicator_of_notMem (show release (1:Y) y∉ C from fun ⟨i,t,r⟩=>v ((release_injOn hy _ (hj t) h r) ▸ t)), smul_zero]
 rw [hy'] at hp; rw [hp,← tape_volume.integral_comp' Z']; change _=∫ y:Z,(Z' ∘ tape) ((Real.sqrt x)⁻¹ • y); rw [Measure.integral_comp_inv_smul_of_nonneg volume _ (Real.sqrt_nonneg x),show Module.finrank ℝ Z=Fintype.card (Fresco G W) from Module.finrank_pi ℝ] <;> rfl

lemma host_dom (θ d:ℝ)(q:0<θ)(v:∀ t:G.Color,‖t‖ ≤ d → 0 ≤ a.J t ∧ a.J t≤2 ∧ ‖t‖/2≤G.chord (G.lieExp t)): ∃ M: Z→ℝ,Integrable M ∧ ∀ u: Z,0 ≤ M u ∧ ∀ β> (0:ℝ),∀ V: PathData G, 0 ≤ hostP G p a D d β V θ u∧ hostP G p a D d β V θ u ≤ M u:=by
 let J':=(limit W:ℕ); let t:ℝ:= Fintype.card F; let w:= (1+t)*4*(J':ℝ)^2
 let K':= θ*p.direct/w
 have hv:0≤ t:=Nat.cast_nonneg _; have hu:0 < (J':ℝ):=Nat.cast_pos.mpr (by unfold J' limit; omega); have hx:0<w:=by unfold w; positivity
 have hs:=p.quadratic_pos; have hκ:0< K':=by unfold K'; positivity
 let b:=(K') • (1:Matrix (Fresco G W) (Fresco G W) ℝ); let L:= (a.scale*2)^Fintype.card F
 have hL:0≤ L:=by unfold L; have := hy.scale; positivity
 have hb:b.PosDef:=Matrix.PosDef.one.smul hκ; refine ⟨fun i=> L*coldFee b i, ((gram_p hb).1).const_mul _,fun u=>⟨mul_nonneg hL (Real.exp_pos _|>.le),?_⟩⟩
 intro β h V; let g:= coupling β; let Y':= tape (G:=G) (g • u); let f:= release (1:Y) Y'; have hR:0<g:= coupling_pos h
 by_cases e:Y'∈ chamber G W d; swap; · unfold hostP; rw [Set.indicator_of_notMem (show tape _ ∉ chamber G W d from e)]; exact ⟨le_rfl,mul_nonneg hL (Real.exp_pos _|>.le)⟩
 have hp(i:F): 0 ≤ a.J (Y' i)∧ a.J (Y' i)≤ 2∧ ‖Y' i‖/2 ≤ G.chord (G.lieExp (Y' i)):= v (Y' i) (by simpa using (show Y' i ∈ closedBall _ d from e i (Set.mem_univ _)))
 have hq:0 ≤ pay a Y':= Finset.prod_nonneg (fun i _=> mul_nonneg hy.scale.le (hp i).1)
 have hj: pay a Y' ≤ L:= (prod_le_prod (s:=univ) (f:=fun i=> a.scale*a.J (Y' i)) (g:=fun _=> a.scale*2) (fun i _=>mul_nonneg hy.scale.le (hp i).1) (fun i _=> mul_le_mul_of_nonneg_left (hp i).2.1 hy.scale.le)).trans_eq (by unfold L; simp only [Finset.prod_const,card_univ]) -- tune
 let T:= crateB G (layOut G f); have ht:0≤T:= sum_nonneg (fun _ _=> sq_nonneg _); let s:=Real.sqrt T
 have hm(i:F) : ‖Y' i‖^2 ≤4*(J':ℝ)^2*T:=by
    have hy : G.chord (f i) ≤ (J':ℝ)*s:= lengthsF G f (Real.sqrt_nonneg _) (fun j v=> (sq_le_sq₀ (G.chord_nonneg _) (Real.sqrt_nonneg T)).mp (le_trans (single_le_sum (f:=fun j=> girth G (layOut G f) j^2) (fun _ _=>sq_nonneg _) v) (Real.sq_sqrt ht |>.symm.le))) i
    have hh: ‖Y' i‖/2≤G.chord (f i):=by simp only [f,release,Pi.one_apply,mul_one]; exact (hp i).2.2
    have hg:= pow_le_pow_left₀ (div_nonneg (norm_nonneg (Y' i)) zero_le_two) (hh.trans hy) 2; rw [mul_pow,show s^2=T from Real.sq_sqrt ht] at hg; linarith -- tune
 have hh: dotProduct u u ≤ β*w*T :=by
    have hg:g^2*dotProduct u u= ∑ i:F, ‖Y' i‖^2:=by rw [←price_square (G:=G) (g • u),smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; ring -- tune unused syntax
    have hv':dotProduct u u*1 ≤ β*(w*T):=by
       have he: g^2*dotProduct u u ≤ w*T:=by rw [hg]; apply le_trans (sum_le_sum (fun i _=>hm i)); rw [sum_const,card_univ,nsmul_eq_mul]; unfold w; change t*_≤ _; nlinarith only [ht,sq_nonneg (J':ℝ),mul_nonneg ht (sq_nonneg (J':ℝ))]
       apply le_trans _ (mul_le_mul_of_nonneg_left he h.le); rw [←mul_assoc,← by_coupling h,inv_mul_cancel₀ (pow_ne_zero _ hR.ne'),one_mul,mul_one]
    rw [mul_one,←mul_assoc] at hv'; exact hv'
 unfold hostP; rw [Set.indicator_of_mem (show _∈chamber G W d from e)]; change 0≤ pay a Y' * _∧ pay a Y'*wealthy G p D β V θ f ≤ _; refine ⟨mul_nonneg hq (Real.exp_pos _|>.le),mul_le_mul hj ?_ (Real.exp_pos _|>.le) hL⟩
 apply Real.exp_le_exp.mpr; unfold b; rw [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]; have he:=show K'*(β*w*T)=θ*β*(p.direct*T) from by unfold K'; field_simp
 have hz:p.direct*T ≤ boxE G V D p (layOut G f):=le_add_of_nonneg_right (sum_nonneg fun _ _=> sq_nonneg _)
 have hf :=mul_le_mul_of_nonneg_left hh hκ.le; rw [he] at hf; linarith only [hf,mul_le_mul_of_nonneg_left hz (show 0≤θ*β by positivity)]
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.host_dom
