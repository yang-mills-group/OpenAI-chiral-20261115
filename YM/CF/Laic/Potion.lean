import YM.CF.Laic.Coil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n c:Side}{ι:Type}[Fintype ι]{k m:ℕ}{Z:Positions ι→Bkg (More n)}{a b:ℝ}
def ear(k:Trip m n)(x y:HopK n):ℕ:= separation (terse x) (terse y)+∑ i:Fin m, dial (terse x) (k i)
lemma ear_m (x y:HopK n)(i j:Slot)(r:Trip m n):notx m (x,i) (y,j) r=ear r x y:=by simp [notx, gear, ear, terse, place_x]
lemma valveF(k m:ℕ)(p:0<a)(h:0≤ b):∃ C:ℝ,0<C ∧ ∀ {n:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{Z:E→ Bkg (More n)}, EnvM k Z 0 b → Z 0=1→∀ (J: Toy m n)(x y:HopK n)(u:Trip m n)(i j:Slot), Allows k (fun t=> mold J x y u (Z t) i j) 0 (C*(Real.exp (a*ear u x y)) *∑ l:Slot, ‖J (x,i) (y,l) u‖) :=by
 let d:=a/(2*((k:ℝ)+1)); have hd:0<d:=by unfold d; positivity
 obtain ⟨u,hu,H⟩:=psalm k h d hd; obtain ⟨v,hv,Q⟩:=channelF k (half_pos p) h; obtain ⟨q,hq,P⟩:= mule k m; let U:=composeCost k q u; let C:=2^k*U*v; have hU:0≤U:=by unfold U composeCost; positivity
 refine ⟨1+C,by unfold C; positivity,?_⟩; intro n E _ _ Z g p' J x y z i j
 let s:=ear z x y; have hr: separation (terse x) (terse y)≤s:= by unfold s ear; omega
 let W(t):Fin m→ group.Color:=fun i=> silt (terse x) (z i) (Z t); let V:=u*Real.exp (d*s)
 have hh : Allows k W 0 V:=allows_pi (show 0≤V by positivity) fun i=> H g _ _ _ ((single_le_sum (f:=fun i=>dial (terse x) (z i)) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans (Nat.le_add_left ..))
 have h' : W 0=0:=funext fun i=>by simp [W,p']
 let L:=Real.exp (a/2*s); have he(l): ‖J (x,i) (y,l) z‖≥0:=norm_nonneg _
 have hz(l:Slot): Allows k (fun t=> J (x,i) (y,l) z (W t)*walkB x y (Z t) l j) 0 (C*Real.exp (a*s)* ‖J (x,i) (y,l) z‖):=by
    let B:=J (x,i) (y,l) z; have he:Allows k B (W 0) (q*‖B‖):=by rw [h']; exact P B
    have hp:Allows k (fun t=> B (W t)) 0 (U*L* ‖B‖):=by
      apply (he.comp hh).mono; apply (eGrowth k s hd (mul_nonneg hq (norm_nonneg _)) hu.le (d:=a/2) ?_).trans_eq
      · unfold U L composeCost; ring
      have hX:d*(k+1:ℝ)= a/2:=by unfold d; field_simp
      linarith
    refine (hp.bilinear (ContinuousLinearMap.mul ℝ ℂ) (Q g p' x y s hr _ _) (ContinuousLinearMap.opNorm_mul_le ..)).mono (le_of_eq ?_)
    unfold L U C B; rw [show a*(s:ℝ)=a/2*s+a/2*s by ring,Real.exp_add]; unfold U; ring
 have ht :0≤∑ l:Slot, ‖J (x,i) (y,l) z‖:=by positivity
 simp only [mold,Matrix.mul_apply]; apply (allows_sum (s:=univ) (fun i _=> hz i)).mono; simp_rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ ht; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le); linarith
structure Yoke (l:ι→Site c)(F:Positions ι→ Bkg (More n))(z:Site (More n)→ Site c)(B:ℕ) :Prop where
 meter i j: separation (z i) (z j) ≤ B*separation i j
 serves {u v : Positions ι}(i:Edge (Site (More n))): together l (z i.1) B u v → F u i=F v i
lemma hired {z:Site (More n)→ Site c}{B:ℕ}{l:ι→Site c}(p:Yoke l Z z B)(J:Toy m n) (x y:HopK n)(i j:Slot)(t: Trip m n): Requests Set.univ (fun g=> mold J x y t (Z g) i j) l (z (terse x)) (B* (8*(ear t x y+1)+1)):=by
 intro v _ w _ he; let s:=ear t x y; have hp(U:Walk)(h:U.length≤ 8*(s+1)):travel (Z v) (terse x) U=travel (Z w) (terse x) U:=by
    apply path_same; intro i hi; apply p.serves; intro j hj; apply he
    apply (separation_triangle _ (z i.1) _).trans; rw [mul_add B _,mul_one]; exact Nat.add_le_add ((p.meter _ _).trans (Nat.mul_le_mul_left _ (hi.trans h))) hj
 have hs(i:Fin m):dial (terse x) (t i)≤s:= le_trans (single_le_sum (f:=fun i=>dial (terse x) (t i)) (fun _ _=> Nat.zero_le _) (mem_univ i)) (Nat.le_add_left ..)
 have hw:(shiftH (terse x) (terse y)).length≤ 8*(s+1):=by have hl:=short (terse x) (terse y); unfold s ear; omega
 have hz(i: Fin m): silt (terse x) (t i) (Z v)=silt (terse x) (t i) (Z w):=by unfold silt; rw [hp _ (le_trans (leanB ..) (by have h:=hs i; omega))]
 simp_rw [mold,hz,walkB, hp _ hw]
lemma stout(m k:ℕ)(p:0<a)(v:0≤b)(B:ℕ):∃ c C:ℝ,0<c∧0<C ∧∀ {n r:Side}{ι:Type}[Fintype ι]{l:ι→Site r}{Z:Positions ι→ Bkg (More n)}{z:Site (More n)→ Site r}, Yoke l Z z B→ Z 0=1→ EnvM k Z 0 b →∀ (J:Toy m n)(V:ℝ),(∀ i,balance a J i ≤V)→ smooth (cavil J ∘ Z) 0 ∧ CableM l (z ∘ place_x) (z ∘ place_x) c k (cavil J ∘ Z) 0 (V*C):=by
 obtain ⟨C,hc,H⟩:= valveF k m (half_pos p) v; let x:=a/(2*(8*(k+1:ℝ)*((B:ℝ)+1))); let S:= C*Real.exp (9*x*k*B); have hs:0<S:=mul_pos hc (by positivity); have hx:0<x:=by unfold x; positivity
 refine ⟨x,S*(↑(Fintype.card Slot):ℝ),hx, mul_pos hs (by positivity),?_⟩; intro n r ι F l Z z hp hz U J V ht
 have hM:smooth (cavil J ∘ Z) 0:=by
    rintro ⟨i,j⟩ ⟨u,v⟩; change ContDiffAt ℝ ω (fun y=> (∑ t,mold J i u t (Z y)) j v) 0; simp only [Matrix.sum_apply]; exact ContDiffAt.sum fun _ _=>(H U hz J i u _ _ _).analytic
 refine ⟨hM,ledger hM ?_⟩; rintro ⟨i,j⟩ ⟨v,w⟩; let Y:=z (terse i); let O:= z (terse v); let W:=Decay x Y O
 let L(t:Trip m n):= S*nick a (ear t i v)*(∑ k:Slot,‖J (i,j) (v,k) t‖)
 have he(t: Trip m n) : Beacon l x k (fun y=>mold J i v t (Z y) j w) Y 0 (L t*W):=by
   apply ((H U hz J i v t j w).beacon (hired hp J i v _ _ t) univ_mem hx.le).mono
   let A:= ∑ k:Slot,‖J (i,j) (v,k) t‖; have ht:0≤ A:=by positivity
   let q:=ear t i v; have hz:separation Y O≤ B*q:= (hp.meter ..).trans (Nat.mul_le_mul_left _ (Nat.le_add_right ..))
   let V:= Real.exp (a/2*q); let d:=x*(k*(B*(8*(q+1)+1)):ℕ); change C*V*A*Real.exp d ≤ S*nick a q*A*W; rw [mul_right_comm (C*_ ) A,mul_right_comm (S*_ ) A]; apply mul_le_mul_of_nonneg_right _ ht; unfold S V d nick W Push.Uniform.Decay; simp only [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hc.le
   let u:= x* k; apply le_trans (b:=Real.exp (9*(x*((k:ℝ)*B)))*(Real.exp (a*q)*Real.exp (-x*separation Y O))) ?_ ?_
   swap; · -- placeholders
     apply mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (mul_nonneg (by positivity) (by positivity)) (show 1≤1+(q:ℝ) from by simp)) (Real.exp_pos _|>.le)
   simp_rw [← Real.exp_add]; apply Real.exp_monotone; have he:(separation Y O:ℝ)≤(B:ℝ)*q:=by exact_mod_cast hz
   have hv:x*(2*(8*(k+1:ℝ)*((B:ℝ)+1)))=a:=by unfold x; field_simp
   push_cast; nlinarith only [show 0≤ x*B*q by positivity,show 0≤ x*k*q by positivity,show 0≤ x*q by positivity,mul_le_mul_of_nonneg_left he hx.le, congrArg (fun v:ℝ=>v*q) hv] -- tune
 have hh: Beacon l x k (fun y=>∑ t,mold J i v t (Z y) j w) Y 0 (∑ t,L t*W):=beacon_sum (fun t _=>he t) (fun t _=>(H U hz J i v t j w).analytic)
 change Beacon l x k (fun y=> (∑ t,mold J i v t (Z y)) j w) _ _ _; simp_rw [Matrix.sum_apply]; apply hh.mono
 rw [←sum_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le); unfold L; simp_rw [mul_assoc S,← mul_sum]; -- combine separately Slot
 have ht1(t:Slot): ∑ p: Trip m n, nick a (ear p i v) * ‖J (i,j) (v,t) p‖≤ V:=by
    simp_rw [← ear_m i v j t]; exact (single_le_sum (f:=fun y:Single n=>∑ p:Trip m n,nick a (notx m (i,j) y p)*‖J (i,j) y p‖) (fun l _=> Finset.sum_nonneg fun i _=>mul_nonneg (nick_pos _ (notx_zero ..)|>.le) (norm_nonneg _)) (mem_univ (v,t))).trans (ht _)
 rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hs.le; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; exact (Finset.sum_le_sum fun t _=> ht1 t).trans_eq (by simp [mul_comm])
end YM.CF.Laic
