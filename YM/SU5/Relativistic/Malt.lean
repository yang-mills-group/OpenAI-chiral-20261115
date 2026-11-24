import YM.SU5.Relativistic.Velith
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
open MinorPins Precision Exterior Pageant Matrix
variable (G: Gauge){V:Side}
local notation "J"=> Fresco G W_
local notation "H_"=> Ink G N
local notation "Fσ"=> Face (Per N)
def tiltL (p:T_):Link W_ ↪ Link N:= ⟨raise L p,rise_b L p⟩
def porto (p:T_): J ↪ H_:= (crosses G W_).trans ((tiltL L p).prodMap (Embedding.refl _)) -- order
local notation "YU"=> faceCurl
lemma equal_h (p:T_)(v: J→ℝ)(i : Face (Per W_))(h:i∈ ort W_) : faceCurl (zipFace L p i) (drafts G (porto L G p) v)= faceCurl i (brightQ G W_ v):=by
 let e:= porto L G p; let F:= crosses G W_
 have he (u:Link W_)(j:G.ColorIndex): (smear e*ᵥ v) (raise L p u,j)=(smear F*ᵥ v) (u,j):=by
    by_cases h:u∈ livelies W_; · let i:J:= (⟨_,h⟩,j); exact (smear_t (e:=e) v i).trans (smear_t (e:=F) v i).symm
    rw [smear_f,smear_f]; · rintro ⟨t,g⟩; exact h ((show t.1.val=u from congrArg Prod.fst g) ▸ t.1.property)
    rintro ⟨t,g⟩; exact h ((rise_b L p (a₁:=t.1.val) (a₂:=u) (congrArg Prod.fst g)) ▸ t.1.property)
 ext j
 unfold brightQ drafts; rw [atCurl,atCurl]; change Curl (fun m=> (smear e*ᵥ v) (m,j)) (zipFace L p i)= Curl (fun m=> (smear F *ᵥ v) (m,j)) i
 rcases i with ⟨y,⟨⟨a,b⟩,l⟩⟩; unfold Curl zipFace; dsimp only; have u:= mem_filter.mp h; rw [← evenShift L p y a u.2.1, ← evenShift L p y b u.2.2]; rw [show (setDown L p y,a)=raise L p (y,a) from rfl,show (setDown L p y,b)=raise L p (y,b) from rfl,show (setDown L p (y+step a),b)=raise L p (y+step a,b) from rfl,show (setDown L p (y+step b),a)=raise L p (y+step b,a) from rfl]; simp only [he]
lemma gate_cr (p:T_)(v:J→ℝ): ∑ i∈ mounted L p,‖faceCurl i (drafts G (porto L G p) v)‖^2= inCurl G (brightQ G W_ v):=by unfold mounted; rw [sum_map]; exact Finset.sum_congr rfl (fun i h=> by rw [show chip L p i=zipFace L p i from rfl,equal_h L G p v i h])

def outlays(D:ℕ):Finset (Fresco G W_):= univ.filter fun i=>¬deep (2*D+2) i.1.val.1
lemma out_card (D:ℕ): (outlays L G D).card≤32*(2*D+2)*L.count.val^3*Fintype.card G.ColorIndex:=by
 let e:=crosses G W_; let T:= outlays L G D
 have h:T.map e⊆ edgeT W_ (2*D+2) ×ˢ (univ:Finset G.ColorIndex):=by
   intro i u; obtain ⟨j,h,rfl⟩:=mem_map.mp u; exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩, mem_univ _⟩
 have ht:= card_le_card h; rw [card_map,card_product,card_univ] at ht; exact ht.trans (Nat.mul_le_mul_right _ (edge_card ..))
def bridle(D:ℕ)(v:J→ℝ)(i:J):= if i∈ outlays L G D then v i else 0
lemma shroud(D:ℕ)(v:J→ℝ): dotProduct (bridle L G D v) (bridle L G D v)=∑ i∈ outlays L G D,v i^2:=by
 rw [grit,←sum_subset (s₁:=outlays L G D) (subset_univ _)]; · apply Finset.sum_congr rfl; intro i h; unfold bridle; simp [h]
 intro i v h; unfold bridle; rw [if_neg h]; ring
lemma door_wall (p:T_)(D:ℕ)(v:J→ℝ)(i:Fσ)(h:∀ j:J, (porto L G p j).1∈ support i → j∈ outlays L G D) : YU i (drafts G (porto L G p) v)=YU i (drafts G (porto L G p) (bridle L G D v)):=by
 let u:= porto L G p; let A:=smear u *ᵥ v; let P:=smear u *ᵥ (bridle L G D v)
 have hp(j:H_)(w:j.1∈ support i): A j=P j:=by
    by_cases e:j∈Set.range u; · obtain ⟨x,rfl⟩:=e; exact (smear_t (e:=u) v x).trans ((show v x= bridle L G D v x from (if_pos (h x w)).symm).trans (smear_t (e:=u) (bridle L G D v) x).symm)
    exact (smear_f _ _ e).trans (smear_f _ _ e).symm
 ext j; change (YU i (laced G A)) j=(YU i (laced G P)) j; rw [atCurl,atCurl]; unfold Curl; simp (disch := simp [Fixed.Pivots.support,window]) only [hp]
lemma dark_curl (p:T_)(D:ℕ)(v:J→ℝ)(i:Fσ)(e:i∉ mounted L p): YU i (drafts G (porto L G p) v)=YU i (drafts G (porto L G p) (bridle L G D v)):=door_wall L G p D v i fun j h=> mem_filter.mpr ⟨mem_univ _,fun t=>e (doorway L p h (fade_d (2*D+2) 2 (by omega) _ t))⟩

-- global cost
lemma hull_q (v: Ink G V→ℝ): curlE (laced G v) ≤ 96*dotProduct v v:=by
 let Z:= dotProduct v v
 have hp(x:ℝ)(y z w:ℝ): (x+y-(z+w))^2 ≤ 4*(x^2+y^2+z^2+w^2):=by nlinarith [sq_nonneg (x-y),sq_nonneg (x+z),sq_nonneg (z-w),sq_nonneg (x+w),sq_nonneg (y+z),sq_nonneg (y+w)]
 have ht(k:PlaqAxes) : ∑ j:Site V, ‖YU (j,k) (laced G v)‖^2 ≤ 16*Z:=by
   let a:= k.val.1; let b:= k.val.2
   let U(x:Site V)(i:Axis):= ∑ j:G.ColorIndex,(v ((x,i),j))^2
   have hx(x : Site V) : ‖YU (x,k) (laced G v)‖^2 ≤4*(U x a+U (x+step a) b+U (x+step b) a+U x b):=by
      rw [pts]; simp only [atCurl,Curl]; unfold U; simp only [←sum_add_distrib,mul_sum]; exact Finset.sum_le_sum fun _ _=> hp ..
   have he : ∀ (x:Axis)(r:Site V), ∑ i:Site V,U (i+r) x ≤ Z:=by
      intro x r; unfold U Z; rw [←Fintype.sum_prod_type (f:=fun i:Site V × G.ColorIndex => v ((i.1+r,x),i.2)^2),grit]; let f(i: Site V × G.ColorIndex): Ink G V:= ((i.1+r,x),i.2); exact FreeResolvent.Cost.sum_comp_le (f:=f) (by intro i j h; exact Prod.ext (add_right_cancel (congrArg (fun a:Ink G V=>a.1.1) h)) (congrArg (fun a: Ink G V=>a.2) h)) (fun i=>v i^2) (fun _=>sq_nonneg _)
   have ha:=he a 0; have hb:=he b 0; simp_rw [add_zero] at ha hb; refine (sum_le_sum (fun j _=> hx j)).trans ?_; rw [←mul_sum]; simp only [sum_add_distrib]; linarith only [ha,hb,he b (step a),he a (step b)]
 unfold curlE Face; rw [Fintype.sum_prod_type,sum_comm]; change _≤96*Z; refine (sum_le_sum (fun i _=> ht i)).trans_eq ?_
 rw [sum_const,card_univ,nsmul_eq_mul,show Fintype.card PlaqAxes=6 from by decide]; push_cast; ring
variable (W:PathData G)(D:ℕ)
lemma plum_c (x:T_)(v:J→ℝ)(i:Face (Per W_))(h:i∈ plumb W_ D) : cropL G W D (drafts G (porto L G x) v) (zipFace L x i)=cropL G W D (brightQ G W_ v) i:=by
 apply tsum_congr; intro j; dsimp only [zipFace]; split; next g=>
    unfold curling; obtain ⟨p,t⟩:= stitched L D x i.1 (W.row i.2 j).2 g ((mem_filter.mp h).2); rw [p,equal_h L G x v _ t]
 next=> rfl
lemma gate_row(p:T_)(v:J→ℝ): (∑ i∈ plumage L D p,‖cropL G W D (drafts G (porto L G p) v) i‖^2)= shortV G W D (brightQ G W_ v):=by unfold plumage; rw [sum_map]; exact Finset.sum_congr rfl (fun i h=> by rw [show chip L p i=zipFace L p i from rfl,plum_c L G W D p v i h])
lemma dark_row(p:T_)(v:J→ℝ)(i:Fσ)(e:i∉plumage L D p): cropL G W D (drafts G (porto L G p) v) i=cropL G W D (drafts G (porto L G p) (bridle L G D v)) i:=by
 apply tsum_congr; intro j; split; next g=>
    unfold curling; rw [door_wall L G p D v _ (fun a h=> mem_filter.mpr ⟨mem_univ _,fun t=> e (doorway_p L p _ g h t)⟩)]
 next=> rfl

variable {a b σ C' P:ℝ}{K:Bed}{c:Clip}(B:W.Bounds c σ C' P)
include B
lemma combC (x:Ink G V→ℝ) : (∑ i:Face (Per V), ‖cropL G W D (laced G x) i‖^2)≤6*C'^2*96*dotProduct x x:=by
 have he: Fintype.card PlaqAxes=6:=by decide
 let v:= laced G x; have hx:= (tail_G B (curling v) (ticket_q v B.width.le) D).2; rw [he] at hx; push_cast at hx; exact hx.trans ((mul_le_mul_of_nonneg_left (hull_q G x) (by positivity)).trans_eq (by ring))
lemma expense (r:ℝ)(e:0<r)(x:Ink G N→ℝ)(f:Floor K c N a b)(a:Attached K W)(t:(1+1/r)*vane σ C' D ≤ r*c.direct): dotProduct x (hess G K N *ᵥ x) ≤ (1+r)*(c.direct*curlE (laced G x)+ ∑ i:Fσ, ‖cropL G W D (laced G x) i‖^2):=by
 let s:= laced G x
 have hp(i:Fσ) : ‖ellLine W i s‖^2 ≤ (1+r)*‖cropL G W D s i‖^2+(1+1/r)*‖ellLine W i s-cropL G W D s i‖^2:=by
    let l:= ellLine W i s; let h:= cropL G W D s i; have hx:‖l‖≤ ‖h‖+‖l-h‖:= calc _=‖(l-h)+h‖:=by rw [sub_add_cancel]
                                                                                  _ ≤ ‖l-h‖+‖h‖:=norm_add_le _ _
                                                                                  _= _:= add_comm ..
    refine (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans ?_; rw [show (1+r)*‖h‖^2+(1+1/r)*‖l-h‖^2=((1+r)*r*‖h‖^2+(1+r)*‖l-h‖^2)/r from by field_simp; ring]; rw [le_div_iff₀ e]; nlinarith only [sq_nonneg (r*‖h‖-‖l-h‖)]
 rw [tent_h,metric_pair K B a _ _ f]; simp only [real_inner_self_eq_norm_sq,sum_add_distrib,←mul_sum]; change c.direct*curlE s+_≤ _
 have hx:= sum_le_sum (s:=univ) fun i _=>hp i; rw [sum_add_distrib,← mul_sum,← mul_sum] at hx; apply le_trans (add_le_add_right hx (c.direct*curlE s)) -- tune left/right
 let V:=curlE s; have hc: ∑ i:Fσ, ‖ellLine W i s-cropL G W D s i‖^2 ≤ vane σ C' D*curlE s := (tail_G B (curling s) (ticket_q s B.width.le) D).1
 change _ ≤ (1+r)*(c.direct*curlE s+ ∑ i:Fσ, ‖cropL G W D s i‖^2)
 linarith only [mul_le_mul_of_nonneg_left hc (show 0≤1+1/r by positivity),mul_le_mul_of_nonneg_right t (show 0≤ curlE s from sum_nonneg fun _ _=>sq_nonneg _)] -- nonlinear linarith? tune

def Berry (c : Clip)(C' r:ℝ):=1+(1+r)*(c.direct*96+6*C'^2*96)
lemma expense_p (r:ℝ)(e:0<r)(x: Ink G N→ℝ)(f:Floor K c N a b)(a:Attached K W)(t:(1+1/r)*vane σ C' D≤r*c.direct): dotProduct x (hess G K N *ᵥ x) ≤ Berry c C' r*dotProduct x x:=by
 apply (expense G W D B r e x f a t).trans
 have hx:= c.quadratic_pos; apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hull_q G x) hx.le) (combC G W D B x)) (show 0≤1+r by positivity)); unfold Berry; linarith only [show 0≤dotProduct x x from (by rw [grit]; positivity)]
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.expense_p
