import GaugeFieldConstruction.Flourish
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side}{M:Male}{b:Bool}{o:Skye.Seat f}{Q:Op (Single f)}{h:ℝ}{t k r:ℕ}
def liftW(o:Skye.Seat f)(M:Male)(b:Bool)(F:Platter): Fn f:=fun i=> κFlow M b F (spot o i.1.1) (portB i)
lemma PJ_addL(A B C:Fn f):PJ_act Q o (A+B) C=PJ_act Q o A C+PJ_act Q o B C:=by unfold PJ_act; simp only [Pi.add_apply,star_add,add_mul,Finset.sum_add_distrib]
lemma PJ_addR(A B C:Fn f):PJ_act Q o A (B+C)=PJ_act Q o A B+PJ_act Q o A C:=by unfold PJ_act; simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
lemma PJ_wL(c:ℂ)(A C:Fn f): PJ_act Q o (c • A) C= star c*PJ_act Q o A C:=by unfold PJ_act; rw [mul_sum]; simp only [Pi.smul_apply,smul_eq_mul,star_mul', mul_assoc]
lemma PJ_wR(c:ℂ)(A C:Fn f): PJ_act Q o A (c • C)= c*PJ_act Q o A C:=by unfold PJ_act; rw [mul_sum]; simp only [Pi.smul_apply,smul_eq_mul]; apply sum_congr rfl; intro i _; ring
abbrev Sharpe (M:Male)(b:Bool)(F:Platter):=∀ i:Kt,∀ x:Cover, Summable fun r:Lane=>Paw 4 M b r.2 i r.1* F r.1 (x+r.2)
def Stroke (o: Skye.Seat f)(M:Male)(b:Bool)(m:ℕ):Submodule ℂ (Fn f):= Submodule.span ℂ {A|∃ (t:ℕ)(i:Kt)(x:Plane), t ≤ m ∧ A=RedV t o M b x i}
def Troke (o:Skye.Seat f)(M:Male)(b:Bool)(m:ℕ):Submodule ℂ Platter where
 carrier:={F|Sharpe M b F∧ liftW o M b F ∈ Stroke o M b m}
 add_mem':=by
    intro x y a b'; let Z:=liftW o M b; change Sharpe M b x∧ _ at a; change Sharpe M b y∧_ at b'
    refine ⟨fun i j=>?_ ,?_⟩; · exact (Summable.congr (Summable.add (a.1 i j) (b'.1 i j)) fun i=> (mul_add ..).symm)
    change Z (x+y) ∈ _; rw [show Z (x+y)= Z x+ Z y from ?_]; exact Submodule.add_mem _ a.2 b'.2
    funext i; unfold Z liftW κFlow; simp only [Pi.add_apply,mul_add]; exact (a.1 ..).tsum_add (b'.1 ..)
 zero_mem':=by
    refine ⟨fun i x=>?_ ,?_⟩; · simp
    rw [show liftW o M b 0=0 from (by funext i; simp [liftW,κFlow])]; exact Submodule.zero_mem _
 smul_mem':=by
    intro c x h; let Z:=liftW o M b; change Sharpe M b x ∧ _ at h
    have he(j y) (r:Lane): Paw 4 M b r.2 j r.1 * (c • x) r.1 (y+r.2)= c*(Paw 4 M b r.2 j r.1 * x r.1 (y+r.2)):= mul_left_comm .. -- tune implicit
    refine ⟨fun i y=>?_ ,?_⟩; · simp_rw [he]; exact (h.1 i y).mul_left _
    change Z (c • x) ∈ _; rw [show Z (c • x)= c • Z x from ?_]; exact Submodule.smul_mem _ c h.2
    funext i; unfold Z liftW κFlow; simp_rw [he,tsum_mul_left]; rfl
lemma Lψt (i:Plane)(x:Kt)(p:t≤k): LψSeed t i x∈Troke o M b k:=by
 refine ⟨fun a s=>?_, Submodule.subset_span ⟨t,x,i,p,rfl⟩ ⟩
 let V(r:Kt)(y:Cover):=Paw 4 M b y a r*LψSeed t i x r (s+y); refine Summable.of_norm (f:=uncurry V) ((summable_prod_of_nonneg (fun u:Lane=>norm_nonneg (V u.1 u.2))).2 ⟨fun r=>?_,(hasSum_fintype _).summable⟩)
 by_cases hr:x=r; · subst r; unfold V LψSeed; simp only [if_true]; exact Ω_summable t _ _ (PC_pay ..) x i s -- tune
 unfold V LψSeed; simp_rw [if_neg hr,mul_zero,norm_zero]; exact summable_zero
-- polynomial generated amplitude axis, numeric interpolation
private abbrev inX (i:Kt) (f:Cover→ℂ): Platter:=Pi.single i f
private lemma inadd (i:Kt)(f g:Cover→ℂ): inX i (f+g)=inX i f+inX i g:=by ext x; by_cases h:x=i <;> simp [h,inX]
private lemma insub (i:Kt)(f g:Cover→ℂ): inX i (f-g)=inX i f-inX i g:=by ext x; by_cases h:x=i <;> simp [h,inX]
private lemma insm (c:ℂ)(i:Kt)(f:Cover→ℂ) : inX i (c • f)= c • inX i f:=by ext x; by_cases h:x=i<;>simp [h,inX] -- simp
private lemma insumm {α:Type*}(t:Finset α)(F:α→ Cover→ℂ)(i:Kt):inX i (∑ v∈t,F v)=∑ v∈t,inX i (F v):=by
 induction t using Finset.induction_on with
 | empty=> simp [inX]
 | insert a t g ih=>rw [sum_insert g,sum_insert g,inadd,ih]
private lemma inδ (i:Kt)(v:Plane)(t:ℕ): inX i (δbook t v)= LψSeed t v i:= by
 funext a x; unfold LψSeed inX; by_cases h:a=i; · subst a; rw [Pi.single_eq_same,if_pos rfl]
 rw [if_neg (Ne.symm h),Pi.single_eq_of_ne h]; rfl
abbrev Seg(k: ℕ): Submodule ℂ (Cover→ℂ):= Submodule.span ℂ {x|∃ (i:ℕ)(v:Plane),i ≤ k ∧ x=δbook i v}
private lemma γe (x:Axis)(v:Cover):rom v (Pi.single x (1:ℝ))= v x:=by rw [rom_p]; rw [sum_eq_single x,Pi.single_eq_same,mul_one]; intro i _ h; simp [h]; simp
abbrev yDig (x:Axis) : Cover→ℂ:= fun i=> ((i x:ℤ):ℂ)
lemma Gold_l (x:Axis)(g:1 ≤ k): yDig x∈ Seg k:=by
 let P:Plane:=Pi.single x (1:ℝ); have hz:δbook 1 P ∈ Seg k:= Submodule.subset_span ⟨1,P,g,rfl⟩
 have he: (-Complex.I) • δbook 1 P=yDig x:= by
    funext y; unfold δbook yDig; rw [Pi.smul_apply,smul_eq_mul,γe]; -- tune double unfold
    simp [←mul_assoc]
 exact he ▸ Submodule.smul_mem (Seg k) _ hz
lemma Gold_m (x y:Axis)(g:2 ≤ k): yDig x*yDig y∈ Seg k:=by
 let i:Plane:=Pi.single x (1:ℝ); let j:Plane:=Pi.single y (1:ℝ)
 have he(u:Plane): δbook 2 u∈ Seg k:=Submodule.subset_span ⟨2,u,g,rfl⟩
 have hv: (1/2:ℂ) • (δbook 2 i+δbook 2 j-δbook 2 (i+j))=yDig x * yDig y:=by
    funext t; unfold δbook yDig; simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply, smul_eq_mul,map_add, show rom t i= _ from γe x t, show rom t j=_ from γe y t]; push_cast; ring_nf; simp [Complex.I_sq] -- tune
 exact hv ▸ Submodule.smul_mem (Seg k) _ (Submodule.sub_mem _ (Submodule.add_mem _ (he _) (he _)) (he _))
lemma quarter (u:ℂ): (fun _=>u)∈ Seg k:=by
 have he : δbook 0 0 ∈ Seg k:=Submodule.subset_span ⟨0,0, Nat.zero_le _,rfl⟩; have hv:u • δbook 0 0=(fun _=>u):=by ext; simp [δbook]; -- indentation tune
 exact hv ▸ Submodule.smul_mem (Seg k) u he
lemma tabv (X: Axis →ℂ)(p:1≤k):FlightFlux.slope X ∈ Seg k:=by
 rw [show FlightFlux.slope X= ∑ i:Axis,X i • yDig i from (by funext x; unfold FlightFlux.slope; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; change (x i:ℝ) • X i = X i*((x i):ℂ); rw [Complex.real_smul,Complex.ofReal_intCast,mul_comm])]; exact Submodule.sum_mem _ (fun i _=> (Seg k).smul_mem _ (Gold_l i p))
lemma term_E (p:Axis→Axis→ℂ)(v:2≤k): FlightFlux.ticket p∈ Seg k:=by
 let f(i j:Axis):= ( (p i j/2) • (yDig i*yDig j)-(p i j*(hit i j:ℂ)/2) • yDig i); have hf:∑ i:Axis,∑ j:Axis,f i j=FlightFlux.ticket p:=by
    funext x; rw [Finset.sum_apply]; unfold FlightFlux.ticket; refine sum_congr rfl fun i _=> ?_; rw [Finset.sum_apply]; refine sum_congr rfl fun j _=>?_ ; unfold f; simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply]; unfold telescope yDig digit; rw [Complex.real_smul]; push_cast; ring
 rw [←hf]; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.sub_mem _ ((Seg k).smul_mem _ (Gold_m i j v)) ((Seg k).smul_mem _ (Gold_l i (by omega)))
lemma Seg_P {p:Cover→ℂ}(g:k ≤2)(h:Paper (k+1) p):p∈ Seg k:=by
 interval_cases k
 · obtain ⟨c,h⟩:= (paper_firm p).mp h; exact h ▸ quarter _ -- orientation
 · rw [← FlightFlux.dock_sewn _ h]; exact (Seg _).add_mem (quarter _) (tabv _ le_rfl)
 rw [← hitch_sewn _ h]; exact (Seg _).add_mem ((Seg _).add_mem (quarter _) (tabv _ (by decide))) (term_E _ le_rfl)
lemma Seg_leg {p:Platter} (g:k≤2)(v:∀ i,Paper (k+1) (p i)): p∈ Troke o M b k:=by
 rw [show p=∑ i:Kt,inX i (p i) from (by funext x; rw [Finset.sum_apply,sum_eq_single x]; simp [inX]; intro i _ h; simp [inX,h,Ne.symm h]; simp)]; refine Submodule.sum_mem _ (fun i _=>?_)
 let T:=Troke o M b k
 have he(Y:Cover→ℂ)(u:Y∈ Seg k): inX i Y∈ T:=by
    induction u using Submodule.span_induction with
    | mem x h=> obtain ⟨t,v,p,rfl⟩:=h; rw [inδ]; exact Lψt _ _ p
    | zero=> rw [show inX i 0=0 from (by simp [inX])]; exact T.zero_mem
    | add i j _ _ p q=> rw [inadd]; exact T.add_mem p q
    | smul x t _ h => rw [insm]; exact T.smul_mem _ h
 exact he _ (Seg_P g (v i))
theorem twoStroke {A B:Fn f}{i j:ℕ}(p:SentK o Q)(e:quote_B M Q o h k)(v:100<f.val)(g:h≠0) (w:A∈Stroke o M false i)(a:B∈ Stroke o M true j)(t:i+j < k)(hK:k≤3): PJ_act Q o A B=0:=by
 induction w using Submodule.span_induction with
 | zero=> exact zero_PJl _
 | mem x H=>
    obtain ⟨r,u,b,w,rfl⟩:=H
    induction a using Submodule.span_induction with
    | zero=> exact zero_PJr _
    | mem y H=> obtain ⟨r',u',b',w',rfl⟩:=H; exact alone_Φ p e v g u u' b b' r r' hK (by omega)
    | add x y s p h g=> rw [PJ_addR,h,g,add_zero]
    | smul v x s h=> rw [PJ_wR,h,mul_zero]
 | add x y s p h g=> rw [PJ_addL,h,g,add_zero]
 | smul v x s h=> rw [PJ_wL,h,mul_zero]
private lemma asepit (F:Cover→Mill→ℂ) (l:List Axis)(x: Cover)(i:Mill): loom l F x i= loom l (fun x=> F x i) x:=by induction l generalizing x with|nil=>rfl|cons a l ih=>rw [loom_cons,loom_cons]; change loom l F (_+_) i-loom l F _ i=_; rw [ih,ih]; rfl
lemma RightCH (i:ℕ)(v:i≤2)(b:Bool)(G:Ratio c f)(x:Mill): (fun j:Single f=> Stove M G (AnchorN o) b i (spot o j.1.1) (portB j) x)∈ Stroke o M b i:=by
 let A:=AnchorN o; let X:=Toy M G A b i; let P:=fun j p=> X j p x; have hp(j:Kt): Paper (i+1) (X j):=by
    unfold X
    interval_cases i
    · exact curb_paper (Ytab M G A b j)
    · change Paper (1+1) (slopeK (Ytab M G A b j)); unfold slopeK; apply slope_paper
    change Paper (2+1) (ticketK (Ytab M G A b j)); unfold ticketK; apply ticket_paper
 have ht: P ∈ Troke o M b i:= Seg_leg v (by
    intro k l v; funext y; unfold P; rw [← asepit, hp k l v]; rfl)
 change _ ∧ liftW o M b P∈ Stroke o M b i at ht; exact ht.2 -- tune Prop meta
end Boom
end YM.CF.TableF
end
