import YM.CF.DPress.FD.Warp.Move
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Cube Lat Scroll Tw Finset
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{I X Y K:Type*}{r m:ℕ}
namespace Tw
abbrev lyng(n:Side):Tw n SU.E:= ⟨fun s k=> polarT s.charge k,rfl,fun a b x=> by rw [polar_t,Bool.xor_comm]; rfl ⟩
abbrev gate(n:Side):=arr (pos n) (lyng n)
abbrev Reign(n:Side):= Seat n→SU.E
lemma gate_e (s:Sweep n)(g:Reign n)(i):(gate n).mv s g i= polarT s.charge (g (boxA s i)):=by change polarT s.charge (g ((pos n).mv s⁻¹ i)) = _; rw [pos_y] -- precedence
lemma dist_rank (b:Bool)(u v:Key): dist (windX b u) (windX b v)=dist u v:=by cases b; rfl; exact Reef.chill.dist_map .. -- tune
abbrev lux(n:Side):Tw n Key:= ⟨fun s k=>windX s.charge k, rfl,fun a b x=> by change windX _ (windX _ x)=windX (Bool.xor _ _) x; rcases a with ⟨s,i,d⟩; rcases b with ⟨t,j,c⟩; cases d <;> cases c <;> simp [windX]⟩ -- tune binder b shadow
lemma wind_v (b:Bool)(g: E): windX b (fund g)=fund (polarT b g):=(polar_val b g).symm
lemma wind_h (b:Bool)(r:ℝ)(A:Key): windX b (r • A) = r • windX b A:=by cases b; rfl; exact cc_rsmul ..
lemma rank_e : Involutive (windX (n:=F) true):= fun i=> cc_cc _ -- precedence
lemma lux_iso (s:Sweep n): Isometry ((lux n).mv s):= Isometry.of_dist_eq (dist_rank s.charge)
variable {K: Type*}[Fintype K]
lemma arrT[PseudoMetricSpace Y](P:Tw n K)(Q:Tw n Y)(h:∀ s, Isometry (Q.mv s)) (s:Sweep n): Isometry ((arr P Q).mv s):=by
 have ht(s:Sweep n)(f g:K→Y): dist ((arr P Q).mv s f) ((arr P Q).mv s g)≤dist f g:=by
    apply (dist_pi_le_iff dist_nonneg).2; intro i; exact ((h s).dist_eq (f (P.mv s⁻¹ i)) (g (P.mv s⁻¹ i))).trans_le (dist_le_pi_dist ..)
 refine Isometry.of_dist_eq (fun i j=>le_antisymm (ht s i j) ?_); exact (show _= dist ((arr P Q).mv _ _) ((arr P Q).mv _ _) from (by rw [(arr P Q).vert s,(arr P Q).vert s])).trans_le (ht s⁻¹ _ _)
abbrev Dry(K:Type*)(n:Side):Tw n K:=⟨fun _ x=>x,rfl,fun _ _ _=>rfl⟩
abbrev sung(X:Tw n I)(T:Tw n Y):Tw n (I⊕Y):=⟨fun s=>Sum.map (X.mv s) (T.mv s),funext fun i=>by cases i <;> simp [X.one,T.one],fun s t x=> by cases x<;>simp [X.pair,T.pair]⟩
/-- plus five layers of fresh rows (at heights `0,...,4`, each group block) -/
abbrev Front(n:Side):= Seat n ⊕ Fin 5
abbrev front(n:Side):Tw n (Front n):= sung (pos n) (Dry _ _)
local notation "L"=> Front n
abbrev chart (n:Side):Tw n (ArrayF (Front n)):= arr (front n) (lux n)
abbrev rug(n:Side) := ArrayF (Front n)
lemma neat(s:Sweep n):Isometry ((chart n).mv s):= arrT _ _ (lux_iso (n:=n)) s
lemma sailX (s:Sweep n)(A:rug n) (u:E): (chart n).mv s (sail A u)=sail ((chart n).mv s A) (polarT s.charge u):= funext fun i=>by unfold chart; change windX s.charge (A _ * fund u)= _*_; rw [win_m,wind_v]; rfl
lemma tiltX(s:Sweep n)(i:Key)(u:i∈Row.tilt):windX s.charge i∈ Row.tilt:=by
 obtain ⟨⟨i,A⟩,p,rfl⟩:=u; refine ⟨(i,polarT s.charge A),⟨p.1,Set.mem_univ _⟩,?_⟩; change i • _ = windX _ (i • fund A); rw [wind_h,wind_v]
lemma sheetX(s:Sweep n){A:rug n}(p:A∈Frame _): (chart n).mv s A∈Frame _:=by
 refine ⟨fun i=> tiltX s (A _) (p.1 _),?_⟩; obtain ⟨i,g,t⟩:=p.2; refine ⟨(front n).mv s i,polarT s.charge g,?_⟩; rw [←wind_v,t]; exact congrArg _ (by change A i=A _; rw [(front n).vert s]) -- tune
lemma fitX (s:Sweep n){r:ℝ}{A B:rug n}(u:Fits r A B): Fits r ((chart n).mv s A) ((chart n).mv s B):=by obtain ⟨y,v⟩:=u; refine ⟨polarT s.charge y,?_⟩; rw [←sailX,(neat s).dist_eq]; exact v
-- membership rotation
abbrev leaf(n:Side)(m:ℕ):=leafL (More n) m
abbrev pullW(n:Side)(m:ℕ): Tw n (leaf n m) := arr (pos n) (Dry _ _)
abbrev Ω(s:Sweep n)(U:rug n):= chart n|>.mv s U
abbrev ωr (s:Sweep n)(U:leaf n m):= (pullW n m).mv s U
lemma ω_e(s:Sweep n)(i)(x:leaf n m): ωr s x i=x (boxA s i):=by change x ((pos n).mv s⁻¹ i)=_; rw [pos_y]
lemma ω_S(s:Sweep n)(x:leaf n m): supportT (ωr s x)=ζ s⁻¹ (supportT x):=by ext i; rw [mem_T,mem_h,mem_h,ω_e]
lemma ω_L(s:Sweep n){x:leaf n m}(t:Live x):Live (ωr s x):=by obtain ⟨i,h⟩:=t; refine ⟨(pos n).mv s i,?_⟩; rw [ω_e]; change x (boxA s ((boxA s).symm i)) = _; rwa [Equiv.apply_symm_apply]
lemma ω_f(s:Sweep n){x:leaf n m}{D:Support (More n)}(v:x∈facet D): ωr s x ∈facet (ζ s⁻¹ D):=by refine ⟨ω_L s v.1,?_⟩; rw [ω_S]; exact ζmono s⁻¹ v.2
lemma ω_b(s:Sweep n){x:leaf n m}{D:Support (More n)}(v:x∈boundary D): ωr s x∈boundary (ζ s⁻¹ D):=by refine ⟨ω_L s v.1,?_⟩; rw [ω_S]; exact map_ssubset_map.mpr v.2
lemma ωT(s:Sweep n)(x y:leaf n m): δR (ωr s x) (ωr s y)= δR x y:=by
 have he(s:Sweep n)(x y:leaf n m): Ramp.d (ωr s x) (ωr s y) ≤ Ramp.d x y:= (dusk ..).2 fun i=> (by rw [ω_e,ω_e]; exact Ramp.tick x y (boxA s i)); apply le_antisymm; refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (he s x y)) (by positivity); apply div_le_div_of_nonneg_right _ (by positivity:_≥_ ); exact Nat.cast_le.mpr (by simpa only [ωr,(pullW n m).vert] using (he s⁻¹ (ωr s x) (ωr s y))) -- tune syntax
end Tw
end YM.CF.DPress.FD
