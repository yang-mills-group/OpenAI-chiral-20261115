import YM.CF.Delta.Cost

/-! Simultaneous closeness and assignments transferable without branch restriction. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Fock SU Lat Cube Phase NormedSpace Branch Tenant Function Finset MeasureTheory Filter Lattice
attribute [local instance] opCStarAlgebra
variable {N m B : Side} {p e : ℝ} {U V : Skin m B}
abbrev touchQ (p : ℝ) (x y : Vect) := ‖x‖=1 ∧ ‖y‖=1 ∧ dist x y≤p
lemma minibank (w : ℕ) {e : ℝ} (g : 0<e) : ∃ p:ℝ, 0<p∧∀ l k:List Vect, l.length ≤ w → List.Forall₂ (touchQ p) l k→ ∀ v : Ballot, |‖restrain margin l v.val‖-‖restrain margin k v.val‖| < e := by
  have he (n : ℕ) : ∃ p:ℝ,0<p∧∀ (l k:List Vect) (x : Ballot), l.length=n→List.Forall₂ (touchQ p) l k → |‖restrain margin l x.val‖-‖restrain margin k x.val‖| < e := by
    let Y := Ballot × (Fin n→Ballot); let f := fun x:Y=> ‖restrain margin ((List.finRange n).map (fun i=>(x.2 i).val)) x.1.val‖
    have hF : Continuous f := Continuous.norm (strain_cont margin margin_pos (List.finRange n) (fun i (x:Y)=> (x.2 i).val) (fun i _=>continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)) _ (continuous_subtype_val.comp continuous_fst)) -- tune
    obtain ⟨p,h,H⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hF) e g
    refine ⟨p/2,half_pos h,?_⟩; intro l k x t V
    obtain ⟨q,v⟩:=List.forall₂_iff_get.mp V
    let L (i:Fin n) := l.get ⟨i.val,t.symm ▸ i.isLt⟩; let K (i:Fin n) := k.get ⟨i.val,(q.symm.trans t).symm ▸ i.isLt⟩
    have hv i : touchQ (p/2) (L i) (K i) := v _ _ _
    let l' (i:Fin n) : Ballot := ⟨L i, by simp [Sphere,(hv i).1]⟩; let k' (i:Fin n) : Ballot := ⟨K i,by simp [Sphere,(hv i).2.1]⟩
    have ht : dist (x,l') (x,k') < p := by rw [Prod.dist_eq,max_lt_iff,dist_self]; exact ⟨h, (dist_pi_lt_iff h).mpr fun i=> (show dist (l' i) (k' i)≤ p/2 from (hv i).2.2).trans_lt (half_lt_self h)⟩
    have hx : |f (x,l')-f (x,k')|<e := H (show dist ((x,l'):Y) ((x,k'):Y)<_ from ht)
    have hw A (p : (A:List Vect).length=n): (List.finRange n).map (fun i=> A.get ⟨i.val,p.symm ▸ i.isLt⟩)=A := by rw [← List.ofFn_eq_map]; subst p; exact List.ofFn_get _
    change |‖restrain margin ((List.finRange n).map L) _‖-‖restrain margin ((List.finRange n).map K) _‖|< _ at hx
    unfold L K at hx; rw [hw l t,hw k (q.symm.trans t)] at hx; exact hx
  induction w with
  | zero=> obtain ⟨p,h,H⟩:= he 0; exact ⟨p,h,fun l k g e x=>H l k x (le_antisymm g (by omega)) e⟩
  | succ i ih=>
    obtain ⟨p,h,H⟩:=ih; obtain ⟨q,v,M⟩:= he (i+1)
    have hz (l k) (f:List.Forall₂ (touchQ (min p q)) l k) d (m:min p q≤d) : List.Forall₂ (touchQ d) l k := f.imp (fun x y g=>⟨g.1,g.2.1,g.2.2.trans m⟩)
    refine ⟨min p q,lt_min h v,fun l k g e x=>?_⟩; by_cases u:l.length = i+1
    · exact M l k x u (hz l k e _ (min_le_right ..))
    exact H l k (by omega) (hz l k e _ (min_le_left ..)) x
lemma turnTip (s : ArrayF m) (r : Zone) (t : Spot m) {l : List (Ramp m)} (k : l∈permits m t r) (h : CloseP p U V) (e : 0≤p) : List.Forall₂ (touchQ ((l.length:ℝ)*(4*(B.val:ℝ)*p))) (train m B U s t.1 l) (train m B V s t.1 l) := by
  induction l generalizing t with
  | nil=> exact .nil
  | cons v l ih=>
    rcases v with ⟨g,o⟩; obtain ⟨w,f⟩:= permits_iff.mp k
    let K:=4*(B.val:ℝ)*p
    have he := ih g (permits_iff.mpr ⟨moves_tail w, fun _ x=> f _ (List.mem_cons_of_mem _ x)⟩)
    let a := parcel m B U t.1 g.1 o; let b:=parcel m B V t.1 g.1 o
    have hv : Cube.cmp firstF a b≤ K := by
      apply (costsV p firstF U V h.1 _ _).trans
      apply mul_le_mul_of_nonneg_right _ e; exact_mod_cast march_len _ _ o ((separation_comm ..).trans_le (chain_near (show Fits m g.1 t.1 from w.1.1) B)) -- tune
    rw [train,train,List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    have hp x y (j:touchQ ((l.length:ℝ)*K) x y) : touchQ ((((g,o)::l).length:ℝ)*K) (turn a x) (turn b y) := by -- tune
      refine ⟨(turn_norm ..).trans j.1,(turn_norm ..).trans j.2.1, (dist_triangle _ (turn b x) _).trans ?_⟩
      have He : dist (turn a x) (turn b x)≤ K := by rw [dist_eq_norm]; have ht:= turn_price a b x; rw [j.1,mul_one] at ht; exact ht.trans hv
      have H : dist (turn b x) (turn b y) ≤ l.length*K := by rw [dist_eq_norm,←turn_sub,turn_norm,←dist_eq_norm]; exact j.2.2
      apply (add_le_add He H).trans; rw [List.length_cons,Nat.cast_add,Nat.cast_one]; rw [add_mul,one_mul,add_comm]

    have hk : touchQ ((l.length:ℝ)*K) (s g).val (s g).val := ⟨vote_unit _, vote_unit _,by rw [dist_self]; unfold K; positivity⟩
    rw [List.forall₂_cons]; exact ⟨hp _ _ hk, he.imp hp⟩
lemma licence (B : Side) : ∃ p:ℝ,0<p ∧ ∀ m:Side,∀ U V:Skin m B, CloseP p U V→ ∀ r:Zone,∀ t:Spot m,∀ l∈permits m t r,∀ s:ArrayF m,broad<rateF m B U s t l→ margin < rateF m B V s t l := by
  obtain ⟨p,h,v⟩:= minibank 6 (show 0<broad-margin from sub_pos.mpr broad_margin)
  let K:= (6:ℝ)*(4*B.val); have he : 0<K:= by
    unfold K; have hp' : 0 < (B.val:ℝ):= by exact_mod_cast B.property
    positivity
  refine ⟨p/K, by positivity,?_⟩; intro m U V H r t l k s g
  have ht := turnTip s r t k H (by positivity)
  have hp : l.length≤6 := total_len (permits_iff.mp k).1
  have hv : |rateF m B U s t l - rateF m B V s t l|< broad-margin := by
    apply v _ _ (by rw [train_len]; exact hp) (List.Forall₂.imp _ ht)
    intro x y h; refine ⟨h.1,h.2.1,h.2.2.trans ?_⟩
    calc
      _ ≤ 6*(4*B.val*(p/K)) := by
        gcongr; exact_mod_cast hp
      _ = p := by rw [←mul_assoc 6]; change K*(p/K)=p; field_simp
  linarith [abs_lt.mp hv|>.2]

def Licit (B : Side) (p : ℝ) := ∀ m:Side,∀ U V:Skin m B, CloseP p U V→ ∀ r:Zone,∀ t:Spot m,∀ l∈permits m t r,∀ s:ArrayF m,broad<rateF m B U s t l→ margin < rateF m B V s t l
lemma passed (g : Licit B p) (h : CloseP p U V) (x : Cue m) (e : law m B U x≠0) : ZeroF m B V x := fun t k l w=> g m _ _ h _ t l w _ (law_ready m B _ _ t (mem_singleton.mp k) _ w (lt_of_le_of_ne (law_positive ..) e.symm))
lemma passArch (g : Licit B p) (h : CloseP p U V) (x y : Cue m) (e : law m B U x≠0) (q : law m B U y≠0) : ∃ s,Arch m B U x y s ∧ Arch m B V x y s := by
  obtain ⟨s,L⟩ : ∃ s:Cue m, bid m B U x y s≠0 := by by_contra! k; have hp:=bid_norm U x y; simp_rw [k,integral_zero] at hp; exact zero_ne_one hp
  have he := ready_vertex U x y L
  refine ⟨s,bid_ready U x y (law_rich m B _ _ e) (law_rich m B _ _ q) L,checksX V x (passed g h x e) ?_,checksX V y (passed g h y q) ?_⟩
  · intro a l k; exact g m _ _ h _ _ _ k _ (pay m B _ _ _ (a,1) (lt_of_le_of_ne (fund_pos ..) (he a).1.symm) l k)
  intro a l k; exact g m _ _ h _ _ _ k _ (pay m B _ _ _ (a,1) (lt_of_le_of_ne (fund_pos ..) (he a).2.symm) l k)
lemma CloseP.relax (g : CloseP p U V) {q : ℝ} (h : p≤q) : CloseP q U V := ⟨fun x=>(g.1 x).trans h,fun x=>(g.2 x).trans h⟩
structure Wood (B : Side) (p : ℝ) : Prop where
  pos : 0<p
  licit : Licit B p
  pose {m : Side} (e : ℝ) (U V : Skin m B) (h : CloseP p U V) (b : Room B e) (g : Guard U e) (k : Guard V e) {s : ArrayF m} {r} (u:Verified m B margin U s r) (v : Verified m B margin V s r) {q} (t:q∈zone r) (c : Phase.Part m B) : ‖lens m B c U-lens m B c V‖ ≤ 1/16 ∧ ‖bow m B U s q-bow m B V s q‖≤1/16
lemma slip (B : Side) : ∃ p,Wood B p := by
  obtain ⟨p,h,H⟩:=tune B; obtain ⟨q,g,Q⟩:= licence B
  refine ⟨min p q,lt_min h g,fun m U V l=> Q m U V (l.relax (min_le_right ..)),?_⟩; intro m e U V k b g h s r f x q t c; exact H m q U V (k.relax (min_le_left ..)) r s t f x e b g h c
end YM.CF.Delta
