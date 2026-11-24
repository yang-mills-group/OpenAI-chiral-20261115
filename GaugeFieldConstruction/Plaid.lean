import GaugeFieldConstruction.Razel
import GaugeFieldConstruction.Lodes
import GaugeFieldConstruction.Freizes
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
-- nongauge Hot support label
structure BitCost (p:BudgetPoint)(X:Scree.Hub n)(F:InkD n)(h c:ℝ):Prop where
 term: LocalOn X.val.2 F
 fit(V): Flour (camp X.val.2) (F V).val
 measureV:Measurable F
 worth:∃ b: Finset (Dwell n)→ℝ,(∀ i,0≤b i)∧(∀ U, BedP p U F X b)∧ (∑ i:Finset (Dwell n), tariff p X.val.1 h i*b i)≤c
variable {X: Scree.Hub n}{F G: InkD n}{H:Paper n}{h c d:ℝ}
lemma Bpress (B:BitCost p X F h c)(q:∀ (U:Pane n)(g:Agora n),F (GA g U)=paintR false false (tradew n g) (F U)): PressB p X F h c:= ⟨B.term,B.fit,B.measureV,q,B.worth⟩
lemma pressZ (P:PressB p X F h c): BitCost p X F h c:=⟨P.term,P.fitted,P.measureV,P.worth⟩
lemma bitΩ (q:BitCost p X F h c)(v:c≤d): BitCost p X F h d:=by obtain ⟨a,b,l,z,p,t,s⟩:=q; exact ⟨a,b,l,z,p,t,s.trans v⟩
lemma fee_blank : BitCost p X (0:InkD n) h 0:= pressZ (Vale.rinse ..)
lemma add_b(p0:BitCost p X F h c)(q:BitCost p X G h d): BitCost p X (F+G) h (c+d):=by
 obtain ⟨A,t,S,D⟩:=p0.worth; obtain ⟨B,s,Y,E⟩:=q.worth; exact ⟨fun i j h=>congrArg₂ (·+·) (p0.term i j h) (q.term i j h),fun i=> (p0.fit i).add (q.fit i),p0.measureV.add q.measureV, A+B,fun i=>add_nonneg (t i) (s i),fun i u j=> Prism.tack (S i u j) (Y i u j),by simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add D E⟩
lemma sum_b {I:Type*}(T:Finset I)(F:I→ InkD n)(C:I→ℝ)(p':∀ i∈T,BitCost p X (F i) h (C i)): BitCost p X (∑ i∈T,F i) h (∑ i∈T,C i):=by
 induction T using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact fee_blank| @insert i T t ih=>rw [sum_insert t,sum_insert t]; exact add_b (p' i (mem_insert_self ..)) (ih fun j s=> p' j (mem_insert_of_mem s))
-- lift Photon
lemma public_X (x:Wa n)(s:Hubber n)(g:DomainP s x): Flour (camp s) (tokenZ x):=by
 rcases x with _|⟨b,i,j⟩; · exact Flour.grainE
 exact Flour.putPut _ (mem_filter.mpr ⟨mem_univ _,g.1⟩) (mem_filter.mpr ⟨mem_univ _,g.2⟩)
lemma public_G(x: Wa n): Flour univ (tokenZ x):=by rcases x with _|⟨b,i,j⟩; exact Flour.grainE; exact Flour.putPut _ (mem_univ _) (mem_univ _)
noncomputable def civic_K(i:Wa n): Cipher n:=⟨tokenZ i,public_G i⟩
abbrev AlphaY(A:Paper n):InkD n:= fun V=> ∑ i:Wa n,A i V • civic_K i
lemma vibσ(A:Paper n)(V: Pane n): (AlphaY A V).val=∑ i:Wa n,A i V • tokenZ i:=by let L:Cipher n →+ FC (LeanV (Single n)):=⟨⟨Subtype.val,rfl⟩,fun _ _=>rfl⟩; change L (_)=_; unfold AlphaY; rw [map_sum L]; rfl -- crumb
lemma warp_B(p:portable H):∀ (U:Pane n)(g: Agora n),AlphaY H (GA g U)= paintR false false (tradew n g) (AlphaY H U):=by
 intro i g; apply Subtype.ext; symm; rw [vibσ]; let V:=tradew n g; let L:=lotY false false V
 change L (AlphaY H i).val=∑ j,(αLines H (GA g i) j) • tokenZ j; rw [vibσ,p] -- invalid rw
 exact exportV V false false _ -- tune
abbrev partyT : Wa n→ Finset (Dwell n)
 | none=> ∅
 | some (b,i,j)=>{(b,i),(!b,j)}
abbrev partyL: Wa n→ℂ
 | none=>1
 | some (b,i,j)=>parity (b,i) {(!b,j)}
lemma duoM (x:Wa n) :‖partyL x‖=1:=by rcases x with _|⟨b,i,j⟩; exact norm_one; simp [partyL,parity]
lemma ticket_D(x:Wa n): poke (partyT x)=partyL x • tokenZ x:=by
 rcases x with _|⟨b,i,j⟩; · unfold partyL; rw [one_smul]; exact Poly.tag_void _
 have he: ((b,i): LeanV (Single n))∉ ({(!b,j)}:Finset (LeanV (Single n))):=by cases b<;>simp
 exact (Poly.tag_any _ _ _ he).trans (by rw [Poly.tag_once]; rfl)
lemma chip_W(x:Wa n)(y:Finset (Dwell n)): crumb (tokenZ x) y= if y=partyT x then (partyL x)⁻¹ else 0:=by
 have hp:partyL x≠0:=norm_ne_zero_iff.mp (by rw [duoM]; exact one_ne_zero)
 rw [show tokenZ x= _ from (show tokenZ x=(partyL x)⁻¹ • poke (partyT x) from (by rw [ticket_D,smul_smul,inv_mul_cancel₀ hp,one_smul])),crumb_scale,Pastry.chip]; split <;> simp
abbrev quoteF (x:Wa n)(f:Lit n):InkD n:= fun i=> f i • civic_K x
def preFoot(p:BudgetPoint)(u:ℕ):ℝ:= ((1+(u:ℝ))^p.power)^p.order
lemma snapCost (x:Wa n)(Y:Lit n)(z: Micro p X.val.2 Y c)(s:DomainP X.val.2 x){j:ℕ}(v: X.val.2⊆halo j ({X.val.1}:Support (More n))): BitCost p X (quoteF x Y) h (tariff p X.val.1 h (partyT x)*(c*preFoot p j)):=by
 let R:=partyT x; let L:= c*preFoot p j; have he:0≤L:=mul_nonneg z.1 (by unfold preFoot; positivity)
 let V:= X.val; refine ⟨fun i j u=> congrArg (· • civic_K x) (z.2.2.1 _ _ u),fun i=> (public_X _ _ s).smul _, z.2.1.meas.smul measurable_const, Pi.single R L,fun i=>by rw [Pi.single_apply]; split; exact he; exact le_rfl,fun A w r=>?_,?_⟩
 · let q:tangD n→ℂ:=fun g=> crumb (quoteF x Y (increment A g)).val r; have hp(g:tangD n): q g=(Y (increment A g))*crumb (tokenZ x) r:= crumb_scale _ _ _; by_cases f:r=R
   · subst r; rw [Pi.single_eq_same]; let y:tangD n→ℂ:=Y∘ increment A; let a:=(partyL x)⁻¹; change Signs _ _ q _; rw [show q=(a • y) from funext fun i=>by rw [hp i,chip_W x R,if_pos rfl,mul_comm]; rfl]
     have hh :‖a‖=1:=by rw [show a=(partyL x)⁻¹ from rfl,norm_inv,duoM]; simp
     have hG: Signs p X.val.1 y L:= halo_price V.1 _ z.2.2.1 (z.2.2.2 _ w) v
     let M:= a • ContinuousLinearMap.id ℝ ℂ; have hy:=Mew.grade_unit a _ hG; rw [hh,one_mul] at hy; exact hy -- tune
   change Signs _ _ q _; rw [Pi.single_eq_of_ne f,show q=fun _=> 0 from funext fun i=> by rw [hp i,chip_W, if_neg f,mul_zero]]; exact Prism.hail (Eq.le norm_zero)
 apply le_of_eq; rw [sum_eq_single R]
 · rw [Pi.single_eq_same]
 · intro i _ h; rw [Pi.single_eq_of_ne h,mul_zero]
 simp
lemma tariff_W (x:Wa n){j:ℕ}(w: DomainP X.val.2 x)(v:X.val.2⊆halo j ({X.val.1}:Support (More n))): tariff p X.val.1 h (partyT x) ≤ (1+(j:ℝ))^p.power*papW n h x:=by
 rcases x with _|⟨b,i,k⟩
 · change tariff p _ _ ∅≤ _ *1; unfold Scree.tariff endL; simp; try exact one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
 let Q:= partyT (some (b,i,k)); let Z:= X.val
 have he: Q.card=2:=by cases b <;>simp [Q,partyT]
 have hx(a:Seat n)(u:a∈X.val.2): separation X.val.1 a ≤ j:=by obtain ⟨k,s,h⟩:= halo_spec.mp (v u); rw [mem_singleton.mp s] at h; exact h
 have hp:endL X.val.1 Q ≤ j:=by
    apply Finset.sup_le; intro l p; rcases mem_insert.mp p with rfl|g; · exact hx _ w.1
    rw [mem_singleton.mp g]; exact hx _ w.2 -- tune
 change tariff p _ _ Q≤ _; unfold Scree.tariff; rw [he]; change _*_ ≤ _* (h^2); exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr hp) _) _) (sq_nonneg _)
lemma scale_one {j:ℕ}(x:Wa n)(v:X.val.2 ⊆ halo j ({X.val.1}:Support (More n)))(t:Micro p X.val.2 (H x) c)(s:¬ DomainP X.val.2 x→H x=0): BitCost p X (quoteF x (H x)) h (((1+(j:ℝ))^p.power*preFoot p j)*(papW n h x*c)):=by
 by_cases h:DomainP X.val.2 x
 · apply bitΩ (snapCost x _ t h v); apply (mul_le_mul_of_nonneg_right (tariff_W x h v) (mul_nonneg t.1 (by unfold preFoot; positivity))).trans_eq; ring
 rw [s h,show quoteF x 0=0 from funext fun i=>zero_smul ℂ (civic_K x)]; exact bitΩ fee_blank (mul_nonneg (mul_nonneg (by positivity) (by unfold preFoot; positivity)) (mul_nonneg (papW_v ..) t.1))
lemma downCost (u:TrackD p X.val.2 h H c)(v:portable H){j:ℕ}(p':X.val.2 ⊆halo j ({X.val.1}:Support (More n))): PressB p X (AlphaY H) h (((1+(j:ℝ))^p.power*preFoot p j)*c):=by
 obtain ⟨a,f,w⟩:=u; refine Bpress ?_ (warp_B v); let k(i:Wa n): InkD n:= quoteF i (H i); rw [show AlphaY H=∑ i,k i from funext fun i=>Eq.symm (Finset.sum_apply i univ k)]; let Q:=(1+(j:ℝ))^p.power*preFoot p j; apply bitΩ (sum_b univ k (fun i=>Q*(papW n h i * a i)) (fun i _=> scale_one i p' (f i|>.1) (f i|>.2))); rw [← mul_sum]; exact mul_le_mul_of_nonneg_left w (mul_nonneg (by positivity) (by unfold preFoot; positivity))
abbrev crestP :ℝ:= (25:ℝ)^3*((25:ℝ)^3)^6
lemma sprig (U:TrackD p (Pach o) h H c)(s:p.power≤3)(w:p.order ≤6)(v:portable H): PressB p (Zhub o) (AlphaY H) h (crestP *c):=by
 apply lift_PV (downCost (X:=Zhub o) U v (j:=24) (le_refl _))
 rw [show (1+(↑(24:ℕ):ℝ))=(25:ℝ) by norm_num]; have hc:(25:ℝ)^p.power ≤ 25^3:=pow_le_pow_right₀ (by norm_num) s; have ht:preFoot p 24 ≤ ((25:ℝ)^3)^6:=by
    unfold preFoot; rw [show 1+(↑(24:ℕ):ℝ)=(25:ℝ) by norm_num]; exact (pow_le_pow_left₀ (by positivity) hc _).trans (pow_le_pow_right₀ (by norm_num) w)
 exact mul_le_mul_of_nonneg_right (mul_le_mul hc ht (by unfold preFoot; positivity) (by positivity)) (track_pos U)
lemma Alpha_add(V U:Paper n):AlphaY (V+U)=AlphaY V+AlphaY U:=funext fun i=>by simp only [AlphaY,Pi.add_apply, add_smul,sum_add_distrib]
lemma Alpha_s(V:Paper n)(x:ℂ): AlphaY (x • V)=x • AlphaY V:=funext fun i=>by simp only [AlphaY,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]
lemma AlphaØ : AlphaY (0:Paper n)=0:=funext fun i=>by simp [AlphaY] -- tune
abbrev AlphaL : Paper n→ₗ[ℂ] InkD n:= ⟨⟨AlphaY,fun x y=>Alpha_add ..⟩,fun x y=>Alpha_s ..⟩
lemma axis_V (V:Paper n)(s:Sweep n):Fren.Turns s (AlphaY V) (AlphaY (Barber s V)):=by
 constructor; intro W; apply Subtype.ext; symm
 change lotY _ _ _ (AlphaY V W).val = _; rw [vibσ,vibσ]; change lotY _ _ _ (_ )=∑ i,αLines _ _ _ • tokenZ i; rw [boothK]; apply exportV -- tune
end MastTin
end YM.CF.XGarden
end
