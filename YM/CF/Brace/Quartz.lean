import YM.CF.Brace.Palla
/-! At starting level it is the *same* section for the given antiperiodic spin convention; all aliases are in this spin. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B: Side}{s:ArrayF m}{r:Zone}{U :Skin m B}
variable {F:Duet m B}{j:ℕ}{e p:ℝ}
def firstM:Male:=⟨1,odd_one⟩
def northZ(m B:Side):Phase.Part m B:= anticut _
variable (g:enoughV B e p)(H: Room B e)(h:Cane (CSide m B) j firstM e p F)
include g H h
lemma frame_init (u:Guard U e): spar j firstM U=portW (helix _).symm (Phase.lens m B (northZ m B) U):=by
 unfold spar funde; rw [if_pos (show firstM.val=1 from rfl),dome_kernel]; change projector ((love _) (wiel _ _ (northZ m B) U))=_; rw [oriented_love (wiel_ok (northZ m B) H u)]; rfl -- defeq
lemma frame_first(u:Guard U e): IsStarProjection (spar j firstM U):=by rw [frame_init g H h u]; exact carts_p _ (lensP _ H u)
lemma ark_align (u:Guard U e)(v:Verified m B margin U s r)(q:Sq)(g':q∈zone r):
 coneP j firstM U (airing m B U s q)=cartsL (helix _).symm (filled (lens m B (northZ m B) U) (bow m B U s q)):=by
 unfold coneP postC spotC; rw [frame_init g H h u,poet g u H.1 v g']; exact relabelF _ (bow_val (northZ m B) H u v g').2.1 (lensP _ H u)
lemma bridgeK (u:Guard U e)(v:Verified m B margin U s r)(x y:Sq)(hx:x∈zone r)(hy:y∈zone r): F U (airing m B U s x) (airing m B U s y)=Phase.ray m B (northZ m B) U s x y:=by
 let A:=airing m B U s; let Bx:=cube_path r; have hc(q)(p:q∈zone r): Slow U (hook (A q)) _:= kleid g u H.1 v p
 have hu(t)(p':t∈zone r): Complex.exp (F U (A x) (A t))=Complex.exp (Phase.ray m B (northZ m B) U s x t):=by
   obtain ⟨hh,hp⟩:=h.rhythm U u _ (hc _ hx) _ (hc _ p'); apply smul_left_injective ℂ hp; apply hh.trans; -- tune
   rw [show A t= _ from (rfl:A t=airing m B U s t)]; change coneP j firstM U (airing m B U s t)=Complex.exp _ • coneP j firstM U (airing m B U s x); rw [ark_align g H h u v t p',ark_align g H h u v x hx, ←ray_filled _ H u v hx p',carts_s]
 let V := fun q=>F U (A x) (A q); let f:= fun z=> (U,A x,A z)
 have ht: ContinuousOn A (zone r):=by
   intro x hx; let T:=fun z:Sq=>(U,s,z); change ContinuousWithinAt _ _ _; apply ContinuousAt.continuousWithinAt; exact (air_at g u H.1 v hx).comp (f:=T) (show Continuous T from continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
 have hv: ContinuousOn V (zone r):= h.cap.comp (f:=f) (continuousOn_const.prodMk (continuousOn_const.prodMk ht)) (fun i hi=>⟨u,hc _ hx,hc _ hi⟩)
 refine carry_log Bx.isPreconnected hv (ray_contzone (northZ m B) H u v hx) x hx hu ?_ y hy
 have hz:V x=0:= add_eq_left.mp (h.spore U u (A x) (hc _ hx) _ (hc _ hx) _ (hc _ hx)) -- fix
 have hh:= ray_add (northZ m B) H u v hx hx hx; rw [hz]; exact (add_eq_left.mp hh.symm).symm
omit g H h in
lemma risingV (i:Row)(u:ArrayF m)(U:Skin m B)(x:Cue m)(h:∀ j,u (j,i)=x j): airing m B U u (stick i)=starfish m B U x:= by
   have hc (i:Row)(s:ArrayF m)(z:Site (Domain m B))(h:∀ j,s (j,i)=x j) : paint m B U s (stick i) z=∑ a,weight m B z a • freight m B U z a (x a):=by rw [paint,Fintype.sum_prod_type]; apply sum_congr rfl; intro a _; rw [sum_eq_single_of_mem i (mem_univ i),stick,dirac_cash,h]; intro j _ p; rw [empty_cash (show stick i j=0 from by simp [stick,p]),zero_smul]
   funext z; unfold starfish airing; rw [hc i _ z h,hc 0 _ z (fun _=> rfl)]
lemma equal_s (U:Skin m B)(p':Guard U e)(x z)(hz:EdgeP m B U x z):F U (starfish m B U x) (starfish m B U z)= amount m B (northZ m B) U x z:=by
 let v:=twin m x z; have hf:= bridgeK g H h p' (show Verified m B margin U v (insert 1 {0}) from hz) (stick 0) (stick 1) (stick_in 0 (by simp)) (stick_in 1 (by simp))
 rw [risingV 0 v U x (by intro j; rfl), risingV 1 v U z (by intro j; rfl)] at hf; exact hf
lemma price_s(U:Skin m B)(p':Guard U e)(x y)(hx:ZeroF m B U x)(hy:ZeroF m B U y) : F U (starfish m B U x) (starfish m B U y)=logs m B (northZ m B) U x y:=by
 obtain ⟨z,v,t⟩:= arches hx hy
 rw [echoes _ H p' x y z ⟨v,t⟩,Phase.bill,← equal_s g H h _ p' x z v,←equal_s g H h _ p' y z t]; apply eq_sub_of_add_eq
 apply h.spore U p' _ (starK g H.1 p' hx) _ (starK g H.1 p' hy) _
 -- z row1 not generically Verified row0! use airing at row1. equality via paint not packaged.
 let S:=twin m x z; have hZ:= kleid g p' H.1 (show Verified m B margin U S (insert 1 {0}) from v) (stick_in 1 (show (1:Row)∈insert 1 {0} by simp))
 rw [risingV 1 S U z (fun _=> rfl)] at hZ; exact hZ
lemma fundus(U:Skin m B)(p':Guard U e):chant m B j firstM F U=cartsL (helix _).symm (sound m B (northZ m B) U):=by
 let x:=(cue_from U).choose; let X:=starfish m B U x; have hx:= (cue_from U).choose_spec
 have he:= ark_align g H h p' (r:={0}) hx (stick 0) (stick_in _ (mem_singleton_self _))
 have hc:song m B F U X= accord m B (northZ m B) U x:=by
   apply integral_congr_ae; apply Eventually.of_forall; intro y
   unfold herald lyre; by_cases ht: law m B U y=0; simp [ht]
   unfold X; rw [price_s g H h U p' y x (law_rich m B U y ht) hx]
 rw [calm g H.1 h U p' X (starK g H.1 p' hx), rootsD, hc,show coneP _ _ _ X= _ from he, sonic _ H p' hx]; rw [sized,sized, unscaled, carts_s, carts_s,norm_smul,norm_smul,carts_n]; rfl
end YM.CF.Brace
