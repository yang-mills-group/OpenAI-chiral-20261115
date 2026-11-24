import YM.CF.Peaks.Pan
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
def foot (A:Op (Single P)):Op (Iota G):=A.submatrix (switchG G) (switchG G)
lemma foot_add(A B):foot G (A+B)=foot G A+foot G B:=rfl
lemma foot_sub(A B):foot G (A-B)=foot G A-foot G B:=rfl
lemma foot_s(A):foot G (star A)=star (foot G A):=rfl
lemma foot_mul(A B):foot G (A*B)=foot G A*foot G B:=(Matrix.submatrix_mul_equiv _ _ _ (switchG G) _).symm
lemma foot_one:foot G 1=1:=by ext; simp [foot,Matrix.one_apply]
variable {C D:Type*}[NormedAddCommGroup D][NormedSpace ℂ D]
lemma floret (f:Chin P → Op (Single P))(a p e)(he:0<e)(h:Solo a p f e) :
    Crown (badge (legal G e)) (temper G e) (temper G e) a p (fun x=>foot G (f x.val.1)) :=by
  let g : legal G e → Openc (More P) e:= fun x=> ⟨x.val.1,leftL G x.property⟩
  let H x:=(tempo G e).home x; let J:=switchG G
  obtain ⟨F,C,p,q,l⟩:=h
  let C' S(i j: Iota G):= C S (J i) (J j); let F' (S: Seal (Site (More P)))(x:legal G e):= foot G (F S (g x))
  have hh i j:saleM a C' i j =saleM a C (J i) (J j):=rfl
  refine ⟨F',C',fun S=>⟨⟨fun t x=>?_,fun i j=>?_⟩,fun i j V hV γ k=>?_⟩,⟨q.posP,fun i=>?_,fun i=>?_⟩,fun x=>?_⟩
  · change foot G (F S _) *foot G (tradew P _).val=foot G (tradew P _).val * foot G _
    rw [← foot_mul,← foot_mul]; exact congr_arg _ ((p S).frame _ (g x))
  · have hl := (p S).expo (J i) (J j)
    refine ⟨hl.positive,hl.triggered,fun x=>hl.bounded _,fun x y=> (hl.variation (g x) (g y)).trans (mul_le_mul_of_nonneg_left ?_ hl.positive),hl.connected.comp ((continuous_fst.comp continuous_subtype_val).subtype_mk _)⟩
    apply div_le_div_of_nonneg_right (le_add_of_nonneg_right (fare_t ..)) (abs_nonneg _)
  · exact (p S).fuel (J i) (J j) V hV (g ∘ γ) k.fst
  · calc
      ∑ j,saleM a C' i j =∑ j: Single P, saleM a C (J i) j:= by simp_rw [hh]; rw [Equiv.sum_comp]
      _ ≤ _:= q.rows _
  · calc
      ∑ j,saleM a C' j i =∑ j:Single P,saleM a C j (J i):=by simp_rw [hh]; exact Equiv.sum_comp J (fun x=> saleM a C x (J i))
      _ ≤ _:= q.cols _
  · dsimp only; rw [show f x.val.1= _ from l (g x)]; ext i j
    simp only [F',foot,Matrix.submatrix_apply,Matrix.sum_apply]
variable {L:Side} {ι:Type*}
lemma flowers (f:WG ι)(h:Lively f): Save L true true (fun i _ _ G x=> foot G (f i _ x.1)):=by
  obtain ⟨a,r,e,h,p,k,v,T⟩:=h; refine recorded (L:=L) (u:=true) (v:=true) (A:=fun i _ _ G x=> foot G (f i _ x.1)) (k:=v) (fun i N P G he hg=> floret G _ a r e k (T i _ ?_)) h k
  apply hg.trans; rw [G.exact_size]; exact Nat.le_mul_of_pos_right _ G.count.property
-- invoice currency conjugate with input reversal
def icec(x:Coil N P):Coil N P:=(ice x.1,ice x.2)
lemma revI (U:Nom N P): icec (unionP U)=unionP U := by rw [unionP,icec, ice_pr, ice_pr]
lemma jazzI (g:Site (More P)→E)(x:Coil N P): jazz G g (icec x)=icec (jazz G g x):=by rw [jazz,jazz,icec,icec]; simp only [icy_g] -- tune
lemma legal_r {x:Coil N P}{e}(h:x∈legal G e): icec x∈legal G e:=by
  obtain ⟨U,h,p⟩:= h; refine ⟨U,h,?_⟩; rw [←revI U]; simpa only [icec, Prod.norm_def,Prod.fst_sub, Prod.snd_sub,ice_norm] using p -- check `simpa`
def mirrorP (A:Script ι) : Script ι := fun i c f G x=> star (A i G (icec x))
lemma Save.withOpp (u v:Bool)(A:Script ι)(h:Save L u v @A): Save L v u (fun i c f G x=> star (A i G (icec x))) :=by
  obtain ⟨a,c,e,ha,hc,he,w,H⟩:= h
  refine ⟨a,c,e,ha,hc,he,w,fun i N P G hw hv=>?_⟩
  let f(x:legal G e):↑(legal G e):=⟨icec x.val, legal_r G x.property⟩
  refine (H i G hw hv).impose f ?_ ?_ ?_ ?_
  · unfold f icec ice; fun_prop -- inspect
  · intro g d; exact Subtype.ext (jazzI G g d.val).symm
  · intro S x y; change deal G S (icec x.val) (icec y.val)/_=_; simp only [deal, icec,ice_f]; rfl
  intro g he; refine realigns he f fun V h γ p=>?_ ; exact (snowy h (fun z=> (γ z).val.1) p.fst).prodMk (snowy h (fun z=> (γ z).val.2) p.snd)
end YM.CF.Peaks
