import YM.SU5.FiniteGaugeData.Brique.Cellar
import YM.SU5.FiniteGaugeData.Brique.Chair
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Spire Tenant Buffered Fock Fock.Brique Tulip Dial Skye Scree
attribute [local instance] opCStarAlgebra
-- θ turns only the needed Blend with actually reflected orientation. `Peg` freezes k & v eager. 
section
variable {I:Type*}[Fintype I][LinearOrder I]
-- flag Bool false = Full. 
def TapFn (b:Bool)(P:Op I)(x:Wave I): Prop:= ∀ u,acts P u=u → acts (creed b u) x=0
variable {P Q:Op I} {S T:Finset I} {F: FC I} {x:Wave I}{b:Bool}
lemma TapFn.add (p:TapFn b P x)(q:TapFn b Q x)(u:IsStarProjection P)(v:IsStarProjection Q): TapFn b (P+Q) x:= by
 intro k h; let z:=acts P k; let w:=acts Q k; have he:k=z+w:=h.symm.trans (act_add ..); have hz:= p z (by unfold z; rw [←act_mul,(show P*P=P from u.1)]); have hw:= q w (by unfold w; rw [←act_mul,(show Q*Q=Q from v.1)])
 have ht: creed b (z+w)=creed b z+creed b w:=by cases b; exact map_add ..; change star _= star (create z)+ star (create w); rw [map_add,star_add]
 rw [he,ht,act_add,hz,hw,add_zero]
lemma creek (u:Ket I)(b:Bool)(t:withinM S u) : Sector S true (creed b u):=by
 cases b; exact Sector.makeP _ t; exact (Sector.makeP _ t).contr
-- Full survives another factor on disjoint marks
lemma TapFn.away (p:TapFn b P x)(F: FC I)(t:Sector S false F)(q:Cellar T P)(h:Disjoint T S): TapFn b P (acts F x) := by
 intro i v; let D:= creed b i; have hv:= (creek i b (v ▸ q.acts_t i)).apart t h; change D*F=(1:ℂ) • (F*D) at hv; change acts D _=_; rw [←act_mul,hv,one_smul,act_mul F,show acts D x=0 from p i v,map_zero] -- coercions
lemma TapFn.swapped (p:TapFn b P x)(U:UNI I)(y:Wave I): TapFn (!b) (twist U P) (arum U false true y x):= by
 intro i q; let j:= acts (star U.val) i; have ht: i=acts U.val j:=(act_starUnit ..).symm; let T:= arum U false true y; change acts _ (T x)=_
 have hv:= p j (by
    have t:=congrArg (fun x=>acts (star U.val) x) q; rw [← act_starUnit U i,← Fock.swivel,act_unit] at t
    simpa [act_starUnit] using t)
 have hz: T 0=0 := by
    unfold T arum oculus; simp only [ite_true]; have he(p:Bool): Spire.dove p (0: Wave I) =0 := by apply PiLp.ext; intro i; cases p; rfl; exact star_zero ℂ
                          -- tune
    rw [he,he,map_zero,smul_zero]
 have h: acts (theta U (creed b j)) (T x)=0:= (arum_act U false true x y (creed b j)).symm.trans ((congrArg T hv).trans hz)
 rw [ht]; cases b
 · change acts (theta U (create j)) (T x)=0 at h; rw [theta_upV,act_smul] at h; exact (smul_eq_zero.mp h).resolve_left (by simp)
 change acts (theta U (remove j)) (T x)=0 at h; rw [theta_downV,act_smul] at h; exact (smul_eq_zero.mp h).resolve_left (by simp)
end
section
variable {N:Side}
/-- actual targets (no truncation in Store) at one torus. -/
structure Peg (N:Side) where
 e : ℝ
 Ft : Bool→Pane N→ Op (Single N)
 turn (a:Axis)(z:ℤ)(b:Bool)(y:Pane N): Guard y e →Ft (!b) (fling a z N y)= twist (carR a z N) (Ft b y)
variable {w m r:ℕ}{T: Peg N}{F:Mark N}{e d:ℝ}{S S':Support (More N)}
structure Crater (v:ℕ)(d e:ℝ)(T: Peg N)(S: Support (More N))(F: Mark N)(m:ℕ)(b:Bool) : Prop where
 once (x:Fields N) (z:Guard x.2 T.e)(p:F x≠0) : ∃ A:Op (Single N),IsStarProjection A ∧
     ∃ s: Support (More N), Lattice.halo v s⊆S ∧ Cellar (modesIn N s) A ∧ A.trace=m ∧
     TapFn b A (acts (star (F x)) (mateK N)) ∧ ∀ B:Op (Single N), Neighbor v B → ‖B-T.Ft b x.2‖ ≤ d → ‖A*B‖ ≤ e
variable (a:Axis) (z:ℤ){b:Bool}
set_option quotPrecheck false
local notation "U" => Buffered.carR a z N
local notation "X" => fun s:Support (More N) => s.image ((Buffered.plane a z).anon N)
lemma world_self : arum U false true (mateK N) (mateK N)=mateK N:=
 arum_self U false true (Tset N) (touchP N ▸ tickB N) (tickR (Buffered.plane a z) inert (pinLift a) (mirrorX a) N)
lemma refl_guard{x:Fields N}(h:Guard x.2 e): Guard (reflFields a z x).2 e:= keepC inert (Buffered.plane a z) x.2 e h
lemma Crater.reflects (p:Crater w d e T S F m b) : Crater w d e T (X S) (Buffered.reflMark a z F) m (!b) := by
 constructor; intro x g v; let y:=Buffered.reflFields a z x; let Z:=twist U; have ht: Guard y.2 T.e:=refl_guard a z g
 have hf:F y ≠ 0:=fun t=> v ((congrArg (Fock.theta U) t).trans (theta_zero _)); obtain ⟨A,h,s,w',C,Tx,U₀,Tq⟩:= p.once y ht hf
 refine ⟨Z A, ?_, X s,?_, C.twist_t U (refl_modes a z s), (trace_twist ..).trans Tx, ?_, ?_⟩ -- tune
 · exact ⟨by unfold IsIdempotentElem; rw [←map_mul,(show A*A=A from h.1)],by unfold IsSelfAdjoint; rw [←map_star,h.2.star_eq]⟩
 · rw [← reflect_halo a z s w]; exact image_mono _ w'
 · refine (congrArg (TapFn (!b) (Z A)) ?_) ▸ U₀.swapped U (mateK N); rw [arum_act,world_self a z]; change acts (theta _ (star _)) _=_; rw [theta_star]; rfl
 intro B v₀ p
 let D:= twist (star U) B
 have hkg:star (star U)=U:=star_star _
 have hg :B=Z D:=(twist_inv (star U) B).symm.trans (congrArg (fun i:UNI (Single N)=>twist i D) hkg)
 have he : fling a z N y.2=x.2:= fling_invol a z x.2
 rw [hg,← he, T.turn a z b y.2 ht] at p; change ‖Z D-Z _‖ ≤ d at p; rw [←map_sub] at p -- tune
 rw [hg, ←map_mul]; exact (twist_norm ..).trans_le (Tq D (v₀.r_back a z) ((twist_norm U (D-T.Ft b y.2)).ge.trans p)) -- tune
lemma Crater.merger (p:Crater w d e T S F m b)(f:AtSupport false S F){R: Mark N}(q: Crater w d e T S' R r b)(g:AtSupport false S' R)(l:Disjoint S S'):
   Crater w d e T (S∪S') (F*R) (m+r) b:= by
 constructor; intro x ht Hx; have H : F x*R x≠0:= Hx
 obtain ⟨A,h,s,w',C,Tx,U₀,Tq⟩:= p.once x ht (left_ne_zero_of_mul H); obtain ⟨V,h',t,v',C',Ty,U',T'⟩:=q.once x ht (right_ne_zero_of_mul H)
 have hs:= C.stock (modes_monotone (Subset.trans (Lattice.halo_subset ..) w')); have hr:= C'.stock (modes_monotone (Subset.trans (Lattice.halo_subset ..) v')); have hp:= (f.allV x).sector.contr; have hq:= (g.allV x).sector.contr; let B:= A+V
 refine ⟨B,duo_orth h h' (hs.orthProd hr (modes_orth l)),s∪t,?_,(C.stock (modes_monotone subset_union_left)).add (C'.stock (modes_monotone subset_union_right)),by rw [show B=A+V from rfl,Matrix.trace_add,Tx,Ty,Nat.cast_add],?_,fun W e w=>?_⟩
 · rw [Halo_unionB]; exact union_subset_union w' v'
 · change TapFn b (A+V) (acts (star (F x*R x)) (mateK _)); rw [star_mul]
   apply TapFn.add _ _ h h'; rw [act_mul]; exact U₀.away _ hq hs (modes_orth l)
   rw [show star (R x)* star (F x)=_ from (hq.apart hp (modes_orth l.symm)).trans (one_smul ℂ _),act_mul]; exact U'.away _ hp hr (modes_orth l.symm)
 rw [show B=A+V from rfl,add_mul]; exact duo_max (e.expanded C w') (e.expanded C' v') (modes_orth l) (Tq W e w) (T' W e w)
lemma Crater.trivial (p:0≤e) (m:Mark N) : Crater w d e T S m 0 b:= by
 constructor; intro x ht t; refine ⟨0,IsStarProjection.zero _,∅,?_,Cellar.no_room _, by simp,?_, fun H h g=>?_⟩ -- tune free inclusion
 · simp [Lattice.halo]
 · intro k v; rw [act_zero] at v; subst k; cases b; change acts (create (0:Ket (Single N))) _=_; rw [map_zero,act_zero]; change acts (star (create (0:Ket (Single N)))) _=_; rw [map_zero,star_zero,act_zero]
 rw [zero_mul,norm_zero]; exact p
-- erosion cost at root supplied by comparison with actual Blend on all Guard (purchased globally or price function); keep radius & pay once. 
lemma Crater.intro' (_u:0 ≤ d) (η: ∀ x:Fields N, Guard x.2 T.e → F x≠ 0 → ∃ A:Op (Single N),IsStarProjection A ∧ ∃ s: Support (More N), Lattice.halo w s⊆S ∧ Cellar (modesIn N s) A ∧ A.trace=m ∧ TapFn b A (acts (star (F x)) (mateK N)) ∧ ‖A*T.Ft b x.2‖ ≤ e-d) : Crater w d e T S F m b:= by
 constructor; intro x t v; obtain ⟨A,h,R,bH,V,X₀,Y,Zt⟩:=η x t v; refine ⟨A,h,R,bH,V,X₀,Y,fun K u z=>?_⟩
 let W:= T.Ft b x.2; have he: ‖A*K-A*W‖ ≤ d:=by rw [←mul_sub]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.norm_le _)).trans z)
 change ‖A*W‖ ≤ e-d at Zt; linarith only [(norm_sub_norm_le (A*K) (A*W)).trans he,Zt]
lemma Crater.out (p: Crater w d e T S F m false)(x:Fields N)(t:Guard x.2 T.e)(f:F x≠0)(s: ∃ B, Neighbor w B ∧ ‖B-T.Ft false x.2‖ ≤ d) : ∃ A:Op (Single N),IsStarProjection A ∧ A.trace=m ∧ Full A (acts (star (F x)) (mateK N)) ∧ ‖A*T.Ft false x.2‖≤ e+d:= by
 obtain ⟨B,v,h⟩:=s; obtain ⟨A,pS,S',_c,_y,V,W,U₁⟩:=p.once x t f; refine ⟨A,pS,V,W,?_⟩; let x₀:= T.Ft false x.2; have he: ‖A*x₀-A*B‖ ≤ d:=by rw [norm_sub_rev, ←mul_sub]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (pS.norm_le _)).trans h)
 calc _ ≤ ‖A*B‖+d := by change ‖A*x₀‖ ≤ _; linarith only [(norm_sub_norm_le (A*x₀) (A*B)).trans he] -- unfold
      _ ≤ _ := add_le_add_left (U₁ B v h) _
end
end YM.CF.Window.Brique
