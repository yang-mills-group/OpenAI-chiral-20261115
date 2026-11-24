import YM.SU5.LoomForce.FineShape
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Next.Rank.Spindle -- heavy
-- Entries on actual boundary operations. Track radius^6 extra paid using exp lease
variable (B:ℕ) (o:Seat N) (h:2*(B+1)< (More N).val)
local notation "J" => install B o ∘L collectF B o h
local notation "ζ"=> Sheds B
local notation "T!" => Turn B
variable (X:Sa N)
include h

omit h in
lemma chill_point (L : Word B)(i:ζ)(hx:i.1∉L.map Prod.fst): Spindle.stage L (Stern i) =0:=by
  induction L with
  | nil=>rfl
  | cons a L ih=>
     simp only [List.map_cons,List.mem_cons,not_or] at hx
     unfold Spindle.stage; unfold Spindle.stage at ih
     simp [ih hx.2, Stern,Ne.symm hx.1] -- tune
lemma chill_lean (i:ζ)(hx:¬contact o B h X i) : pruning X (J (Stern i))=0:=by
 funext x; change (if _ then J (Stern i) x else 0)= _; split; swap; rfl
 next f=>
    change (if hp:x∈Spindle.Room o B then collectF B o h (Stern i) ⟨x,hp⟩ else 0)=_
    split; swap; rfl
    next p=>
       let L:=word group h (⟨x,p⟩:Dim o B); refine (chill_point B L i fun t=> hx ⟨⟨x,p⟩,mem_filter.mpr ⟨mem_univ _,f⟩,List.mem_toFinset.mpr t⟩)
variable (T:StageTree N d (4*a) v) {i j:Single N} (p:0<a)(d0:0<d)(K:HopeT d b g 3)
local notation "δ" =>T.W X i j
local notation "F"=> pieces T X i j
local notation "D"=> composeCost 3 δ g⁻¹
local notation "u'" => ((4:ℝ)*X.card)
include d0 K
omit h in
lemma value_proj (V U:tangD N): ‖donor F V U‖≤ D*(‖V‖*‖U‖):=by
 let v:=iteratedFDeriv ℝ 2 (F∘increment 1) 0
 let k : Fin 2→ tangD N:=![V,U]; rw [show donor F V U= (2:ℝ)⁻¹ • v k from ?_,norm_smul]
 refine (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; norm_num)).trans ((v.le_opNorm k).trans ?_); rw [show ∏ i:Fin 2,‖k i‖= _ from Fin.prod_univ_two _]; apply mul_le_mul_of_nonneg_right; exact (parts_jet T X K i j d0).norm_le _ (by norm_num); positivity
 change _= _ • (iteratedFDeriv ℝ _ _ _) _; rw [iteratedFDeriv_two_apply]; rfl
omit d0 K
variable (vξ:moored o T)
local notation "Χ"=> contact o B h X
include vξ
omit h in
lemma contact_cheap (v: δ ≠ 0) (Y : Seat N)(p:Y∈X): separation o Y ≤ X.card := by
 have he:o∈X:=by by_contra q; apply v; rw [vξ X q]; rfl
 exact ((T.coat X|>.1 ()|>.expo i j).triggered v|>.1.lim _ he _ p|>.le)
omit vξ h in
lemma cottage_price (i:ζ)(L:Word B): ‖Spindle.stage L (Stern i)‖ ≤ L.length:=by
 induction L with
 | nil=> simp [Spindle.stage]
 | cons a L ih=>
    unfold Spindle.stage
    rw [List.map_cons,List.sum_cons,List.length_cons]; unfold Spindle.stage at ih
    apply (norm_add_le ..).trans; refine (add_le_add (b:=1) ?_ ih).trans_eq ?_
    · split <;> first | (rw [norm_neg]; exact sternNorm ..) | exact sternNorm ..
    push_cast; ring
lemma gentle (t:δ ≠ 0) (G:ζ): ‖pruning X (J (Stern G))‖ ≤ u':=by
 apply (pi_norm_le_iff_of_nonneg (by positivity:(0:ℝ) ≤ 4*X.card)).mpr; intro x
 change ‖(if _ then J (Stern G) x else 0)‖ ≤_
 split; swap; rw [norm_zero]; positivity
 next v=>
    change ‖(if w:x∈Spindle.Room o B then collectF B o h (Stern G) ⟨x,w⟩ else 0)‖≤_
    split; swap; rw [norm_zero]; positivity
    next q=>
       let L:=word group h (⟨x,q⟩:Dim o B); have ht:L.length ≤ 4*X.card:=local_card o B h X _ _ rfl (contact_cheap o X T vξ t x.1 (mem_filter.mp v).2.1)
       exact (cottage_price B G L).trans (by exact_mod_cast ht)

noncomputable abbrev stepValue (F0:Pane N→ℂ)(i j:ζ):= donor F0 (J (Stern i)) (J (Stern j))
noncomputable abbrev charges (F0:Pane N→ℂ):=∑ i:ζ,∑ j:ζ,‖stepValue B o h F0 i j‖ -- arg order?
local notation "C"=> Fintype.card group.ColorIndex
include d0 K
lemma entirety : charges B o h F ≤ ((u'^2*(C:ℝ))^2)*(D*u'^2):=by
 have hf(i j):= (T.coat X|>.1 ()).nonn i j
 have hp :0 ≤ D:= (parts_jet T X K i j d0).nonneg
 let T' := (univ:Finset ζ).filter (contact o B h X)
 let θ(i' j':ζ):= ‖stepValue B o h F i' j'‖
 by_cases q:δ=0
 · have ht:D=0:=by rw [q]; unfold composeCost; ring
   have hm(k l:ζ): θ k l=0:= le_antisymm (show θ k l ≤0 from (value_proj X T d0 K (J (Stern k)) (J (Stern l))).trans_eq (by rw [ht,zero_mul])) (norm_nonneg _)
   change (∑ k:ζ,∑ l:ζ,θ k l) ≤ _; rw [ht]; simp only [hm,sum_const_zero,zero_mul,mul_zero]
   exact le_rfl
 have hc:= flagged_card o B h X (contact_cheap o X T vξ q)
 have he(k l:ζ): θ k l= ‖donor F (pruning X (J (Stern k))) (pruning X (J (Stern l)))‖:= congrArg norm (lone_cost T X K i j d0 _ _)
 have ht(k l:ζ): θ k l ≤ D*u'^2 := he k l ▸ (value_proj X T d0 K _ _).trans (show D*(‖pruning X (J (Stern k))‖ * ‖pruning X (J (Stern l))‖) ≤ _ from ?_)
 swap
 · have hz:=(gentle B o h X T vξ q k); have hp:=(gentle B o h X T vξ q l); rw [pow_two]; gcongr
 have hw(i:ζ)(h':i∉T'):pruning X (J (Stern i))=0:=chill_lean B o h X i (fun v=>h' (Finset.mem_filter.mpr ⟨mem_univ _,v⟩))
 have H(k:ζ): ∑ l:ζ,θ k l ≤ (T'.card:ℝ)*(D*u'^2):=by
     rw [←Finset.sum_subset (subset_univ T')]; swap; · exact fun i _ p=>by rw [he k i,hw i p,map_zero,norm_zero]
 ---
     exact (sum_le_sum (s:=T') fun i _=> ht k i).trans (by simp)
 change (∑ k:ζ,∑ l:ζ,θ k l) ≤_; rw [← Finset.sum_subset (subset_univ T')]; swap; · intro k _ p; refine sum_eq_zero (fun i _=>?_); rw [he,hw _ p,map_zero]; simp
 refine (sum_le_sum fun k _=> H k).trans ?_; rw [sum_const,nsmul_eq_mul,←mul_assoc,←pow_two]; gcongr

omit h K vξ in
lemma trace_cutoff : ∀ᶠ u in 𝓝 (0:tangD N),
    untouched T k (increment 1 u)=∑ i∈univ.filter (fun i:Sa N=>i.card<k),∑ j:Single N,pieces T i j j (increment 1 u):= by
 filter_upwards [tent_germ (N:=N) d0] with i ht
 unfold untouched beforePing; rw [dif_pos (tent_profile d0 _ ht),retain,←Finset.sum_filter,Matrix.trace_sum]
 apply sum_congr rfl; intro s _; simp_rw [pieces,dif_pos (tent_profile d0 _ ht)]; rfl


omit K vξ h d0 in
private lemma combine {I:Type*}(n:Finset I)(F':I→ tangD N→ ℂ)(p:∀ i∈n,ContDiffAt ℝ 2 (F' i) 0) (u v:tangD N):
  (2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ (fun x=>∑ i∈n,F' i x)) 0 u v= ∑ i∈n,(2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ (F' i)) 0 u v := by
 let m:=(![u,v]:Fin 2→ tangD N); have he(G:tangD N→ℂ): fderiv ℝ (fderiv ℝ G) 0 u v =iteratedFDeriv ℝ 2 G 0 m:= (iteratedFDeriv_two_apply G 0 m).symm
 simp_rw [he]; rw [iteratedFDeriv_fun_sum_apply (n:=2) (f:=F') p, _root_.sum_apply,Finset.smul_sum] -- name
local notation "Ψr"=>4* a/2
local notation "S"=> tallyC
abbrev stipend (g :ℝ) := ((Fintype.card group.ColorIndex:ℝ)^2)*4^6*(composeCost 3 1 g⁻¹)
omit h K d0 vξ in
private lemma payEx (p:0<a) : ∃ v:ℝ, 0<v∧ ∀ k:ℕ,(k:ℝ)^6 ≤ v * Real.exp ((4*a/2)*k):=by
 have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 (4*a/2) (by positivity)
 let f (k:ℕ):=(k:ℝ)^6/Real.exp ((4*a/2)*k); have he:Tendsto f atTop (𝓝 0):= (h.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).congr fun n=> by unfold f; change (n:ℝ)^(6:ℝ)*_= _; rw [show (6:ℝ) = ((6:ℕ):ℝ) from rfl,Real.rpow_natCast, neg_mul,Real.exp_neg]; ring -- tune
 obtain ⟨v,z⟩:= he.bddAbove_range
 exact ⟨max 1 v,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun i=>by rw [mul_comm]; exact (div_le_iff₀' (Real.exp_pos _)).mp ((z (Set.mem_range_self i)).trans (le_max_right 1 v))⟩

include p
lemma basis_budget (w:ℝ)(t:0<w)(hc:∀ k:ℕ,(k:ℝ)^6 ≤ w*Real.exp ((4*a/2)*k)) : charges B o h (untouched T k) ≤ w*stipend g*expiry (4*a) v:=by
 let P(X:Sa N):= T.W X; let X0:= univ.filter (fun i:Sa N=> i.card<k); let Ω:= Single N; let X': Finset (Sa N × Single N):= X0 ×ˢ univ
 let u: Sa N × Single N→ Pane N→ℂ :=fun i=> pieces T i.1 i.2 i.2
 have hv: ((untouched T k) ∘ increment 1) =ᶠ[𝓝 (0:tangD N)] fun x=>∑ i∈ X',u i (increment 1 x):=by unfold X'; simp_rw [sum_product]; exact trace_cutoff T d0
 let c:=untouched T k; let A:=w*stipend g; have ht(X:Sa N)(i:Single N):charges B o h (pieces T X i i)≤ A*(Branch.rent (4*a/2) X*(P X i i)):= by
    refine le_trans (entirety B o h X T d0 K vξ) ?_
    unfold A Branch.rent
    have hp:0 ≤ P X i i := (T.coat X|>.1 ()).nonn _ _
    let C0:=composeCost 3 1 g⁻¹; have hκ:0 ≤ C0:=by unfold C0 composeCost; have hc:=K.peta; positivity
    have hK:0 ≤ stipend g:=by unfold stipend; change 0≤ _*C0; positivity
    have ht:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hc X.card) hp) hK
    have hl:P X i i*C0= composeCost 3 (P X i i) g⁻¹:=by unfold C0 composeCost; ring
    unfold stipend at *; unfold P at *; rw [←hl]; unfold C0 at *; linarith only [ht]
 have hs(i j:tangD N): donor c i j= ∑ k∈ X',donor (u k) i j:=by
    -- Jets identity
    unfold donor; simp only [_root_.smul_apply]; rw [(hv.fderiv (𝕜:=ℝ)).fderiv_eq (𝕜:=ℝ)]; exact combine X' (fun i=> u i ∘ increment 1) (fun l _=> (parts_jet T l.1 K l.2 l.2 d0).smooth.of_le (m:= ↑(2:ℕ)) (by decide)) i j
 change (∑ i:ζ,∑ j:ζ, ‖stepValue B o h c i j‖) ≤ _; unfold stepValue; simp_rw [hs]; refine le_trans (sum_le_sum (fun i _=>sum_le_sum (fun j _=> norm_sum_le ..))) ?_
 conv_lhs => arg 2; ext; rw [sum_comm]
 rw [sum_comm]; refine le_trans (sum_le_sum (g:=fun i:Sa N × Single N=> A*(Branch.rent (4*a/2) i.1*(P i.1 i.2 i.2))) (fun i _=> ht i.1 i.2)) ?_
 unfold X'; simp_rw [sum_product,←mul_sum]; refine mul_le_mul_of_nonneg_left (le_trans ?_ (saw_line T vξ (by positivity))) ?_
 · unfold tallyC
   let z(X:Sa N):= ledgerV (T.W X)
   have hz(X:Sa N)(i j):0 ≤ P X i j:= (T.coat X|>.1 ()).nonn _ _
   exact (sum_le_sum (s:=X0) (fun X _=> mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun i _=>Finset.single_le_sum (f:=P X i) (fun j _=> hz X i j) (mem_univ i))) (rent_pos (4*a/2) X).le)).trans (sum_le_sum_of_subset_of_nonneg (f:=fun X:Sa N=> Branch.rent (4*a/2) X*z X) (subset_univ _) (fun i _ _=> mul_nonneg (rent_pos _ _).le (sum_nonneg (fun j _=> sum_nonneg (fun k _=> hz i j k)))))
 have hp:=K.peta.le; unfold A stipend composeCost; positivity

omit d0 K p h vξ in
lemma issued_finger (a b g v d:ℝ)(p:0<a)(h:0<d)(t:HopeT d b g 3):
 ∃ C'> (0:ℝ),∀ {N:Side}(B:ℕ)(o:Site (More N))(T:StageTree N d (4*a) v),moored o T →
   ∀ z:2*(B+1)< (More N).val,∀ k:ℕ, charges B o z (untouched T k) ≤ C':=by
 obtain ⟨c,hc,u⟩:= payEx p; let x:=c*stipend g*expiry (4*a) v; refine ⟨max 1 x, lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
 exact @fun N B o T w z k=> (basis_budget B o z T p h t w c hc u).trans (le_max_right ..)
#print axioms issued_finger
end YM.CF.LitCurrent.Surplus
