import YM.SU5.FiniteGaugeData.Endless.Sabot
import YM.SU5.FiniteGaugeData.Mist.Hike
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Endless.Piper
open Function Filter Metric Finset Lattice Hills Mist Complex
open scoped Topology BigOperators InnerProductSpace
variable {σ:Type} {G H:Hilbert} [DecidableEq σ] {T: Type}[NormedAddCommGroup T]
open Hike Knot Willow
section
variable {M:Type*}[Ring M][Algebra ℂ M]
variable (Ω: H)(F:σ→H.Op)(A:σ→σ→H.Op)(R:List σ)
def keep (F:σ→ H.Op)(A:σ→σ→H.Op)(u: List σ):ℂ:= inner ℂ Ω (TapeT F A u Ω)
-- affine in each stamp i when all else fixed
variable (w: H.Op)(i:σ)(p:H.Op) (a b:ℂ) (h:a+b=1)(q:R.Nodup)
local notation "Fx" x:max=> Function.update F i x
include h q
lemma keep_eval : TapeT (Fx (a • w + b • p)) A R= a • TapeT (Fx w) A R + b • TapeT (Fx p) A R := by
 by_cases z:i∉R
 · have hp(w): TapeT (Fx w) A R=TapeT F A R:= same_tape _ F _ _ R (fun k t=>Function.update_of_ne (fun (c:k=i)=>z (c ▸ t)) _ _) (fun _ _ _ _=>rfl)
   simp_rw [hp]; rw [←add_smul,h,one_smul]
 push Not at z
 induction R with
 | nil=> exact (List.not_mem_nil z).elim
 | cons y R ih=>
   have hg(Z)(s i j) : TapeT Z A (i::j::s)= Z i*(A i j*TapeT Z A (j::s)):=rfl
   by_cases hz:y=i; · subst y
                      cases R with
                      | nil=> simp [TapeT,spool]
                      | cons j t=>
                         have ho:i∉j::t:= List.nodup_cons.mp q |>.1; let U:=TapeT F A (j::t); have he(w): TapeT (Fx w) A (j::t)=U:=same_tape _ F _ _ (j::t) (fun j t=>Function.update_of_ne (fun (c:j=i)=>ho (c ▸ t)) _ _) (fun _ _ _ _=>rfl)
                         rw [hg,hg,hg,Function.update_self,Function.update_self,Function.update_self,he,he,he, add_mul, Algebra.smul_mul_assoc,Algebra.smul_mul_assoc]
   -- R definitely has i. (Tape recursive)
   have hh:i∈ R:= (List.mem_cons.mp z).resolve_left (Ne.symm hz); cases R with
   | nil=>exact (List.not_mem_nil hh).elim
   | cons j t => rw [hg,hg,hg,Function.update_of_ne hz,Function.update_of_ne hz,Function.update_of_ne hz, ih (List.nodup_cons.mp q).2 hh]; simp_rw [mul_add,Algebra.mul_smul_comm] -- tune
lemma keep_affine : keep Ω (Fx (a • w + b • p)) A R=a*keep Ω (Fx w) A R+b*keep Ω (Fx p) A R:=by unfold keep; rw [keep_eval F A R w i p a b h q,_root_.add_apply,_root_.smul_apply,_root_.smul_apply,inner_add_right,inner_smul_right,inner_smul_right] -- order
end
section
variable (Ω:H)(F:σ→H.Op)(A:σ→σ→H.Op)(R:List σ)(q:R.Nodup)
variable (ν:G)(D:σ→G.Op)(B:σ→σ→G.Op)(S:List σ)(v:S.Nodup)
variable (c:Set ( ℂ × ℂ))(h: Convex ℝ c)
local notation "pA" F:max=>keep Ω F A R
local notation "pB" F:max=>keep ν F B S
local notation "zA" i:max f:max=> Function.update F i f
local notation "zB" i:max f:max=> Function.update D i f
abbrev relation (Ω:H)(A:σ→σ→H.Op)(R:List σ)(ν:G)(B:σ→σ→G.Op)(S:List σ)(c:Set ( ℂ × ℂ))(F:σ→H.Op)(D:σ→G.Op) := (keep Ω F A R,keep ν D B S)∈c
local notation "C" => relation Ω A R ν B S c
include v q h
lemma keep_conv (i:σ)(t:Knot T){P:T→Prop}(g:T→H.Op)(w:T→G.Op) (k:Covers P t) (p:∀ t:T,P t→ relation Ω A R ν B S c (zA i (g t)) (zB i (w t))) : C (zA i (t.eval g)) (zB i (t.eval w)):=by
 induction t with
 | pin t=>exact p _ k
 | turn x y a b hx hy s ih ig=>
    let u:=(pA (zA i (x.eval g)), pB (zB i (x.eval w))); let U:=(pA (zA i (y.eval g)),pB (zB i (y.eval w)))
    obtain ⟨l,m⟩:=(show Covers P x∧ Covers P y from k); have he: a • u+b • U∈c:=h (ih l) (ig m) hx hy s
    have hw:(a:ℂ)+b=1:= (ofReal_add ..).symm.trans ((congrArg ((↑):ℝ→ℂ) s).trans ofReal_one)
    unfold relation; simp only [eval.eq_2]; rw [keep_affine Ω F A R _ i _ a b hw q, keep_affine ν D B S _ i _ a b hw v]; exact he -- tune pair SCalar
variable (Q:T→ Prop) (V:σ→ T→ H.Op)(U:σ→T→G.Op)
variable (t:σ→Knot T)(x:σ→T)(p:∀ (x:σ→T), (∀ i,Q (x i))→ relation Ω A R ν B S c (fun i=> V i (x i)) (fun i=> U i (x i)))
include p
private lemma relation_subs (Z:List σ)(e:∀ i∈Z,Covers Q (t i)) (m:∀ i,Q (x i)) : let F(i:σ):= if i∈Z then (t i).eval (V i) else V i (x i); let D(i:σ):= if i∈Z then (t i).eval (U i) else U i (x i); C F D:=by
 induction Z generalizing x with
 | nil=> simp_rw [List.not_mem_nil, if_false]; exact p x m -- tune simpl
 | cons i Z ih=>
      intro F D; have hv:=e i (by simp); let F'(i:σ):=if i∈Z then (t i).eval (V i) else V i (x i); let D'(i:σ):= if i∈Z then (t i).eval (U i) else U i (x i); have wx:∀ j:σ,j≠i→ F j=F' j∧ D j=D' j:=by intro j s; simp [F,F',D,D',s]
      have he(a)(v:F i=a): F=Function.update F' i a:=funext fun j=>by
         by_cases p:j=i; · subst j; rw [Function.update_self,v]
         rw [Function.update_of_ne p]; exact (wx j p).1
      have he'(a)(v:D i=a): D=Function.update D' i a:=funext fun j=>by
         by_cases p:j=i; · subst j; rw [Function.update_self,v]
         rw [Function.update_of_ne p]; exact (wx j p).2
      by_cases hZ:i∈Z; · rw [he (F' i) (by simp [F,F',hZ]), he' (D' i) (by simp [D,D',hZ])]; simp only [Function.update_eq_self]; exact ih x (fun i v=>e i (List.mem_cons_of_mem _ v)) m -- tune order
      rw [he ((t i).eval (V i)) (by simp [F]), he' ((t i).eval (U i)) (by simp [D])]; apply keep_conv Ω F' A R q ν D' B S v c h i _ (V i) _ hv; intro b g; let y:=Function.update x i b; have hg:∀ j,Q (y j):=by
         intro j; by_cases p:j=i; · subst j; rw [show y i=b from Function.update_self ..]; exact g
         rw [show y j=x j from Function.update_of_ne p _ _]; exact m j

      let L:= ih y (fun j v=> e j (List.mem_cons_of_mem _ v)) hg; have hy: ∀ j≠i, y j=x j:=fun j p=>Function.update_of_ne p _ _
      rw [show Function.update F' i (V i b) = fun j:σ=>if j∈ Z then (t j).eval (V j) else V j (y j) from ?_, show Function.update D' i (U i b) = fun j:σ=> if j∈ Z then (t j).eval (U j) else U j (y j) from ?_]; exact L
      · ext1 j; by_cases p:j=i; · subst j; simp [y,hZ]
        rw [Function.update_of_ne p]; simp [hy _ p,D']
      ext1 j; by_cases p:j=i; · subst j; simp [y,hZ]
      rw [Function.update_of_ne p]; simp [hy _ p,F']
lemma relation_full (e:∀ i,Covers Q (t i))(mx:∀ i,Q (x i)): C (fun i=> (t i).eval (V i)) (fun i=> (t i).eval (U i)):= by
 let Z:=R++S; let f(i:σ):= if i∈Z then (t i).eval (V i) else V i (x i); let d(i:σ):=if i∈Z then (t i).eval (U i) else U i (x i); suffices relation Ω A R ν B S c f d by
   unfold relation keep at *; rw [same_tape _ f _ _ R (fun i t=> (if_pos (List.mem_append_left _ t)).symm) (fun _ _ _ _=>rfl),same_tape _ d _ _ S (fun i t=> (if_pos (List.mem_append_right _ t)).symm) (fun _ _ _ _=>rfl)]; exact this
 exact relation_subs Ω A R q ν B S v c h Q V U t x p Z (fun i _=>e i) mx
end
section
variable (Ω: H)(F:σ→H.Op)(A:σ→σ→ H.Op)(R:List σ)(p:R.Nodup) (Q:Willow H T)
abbrev Cargo(Z:T): H.Op:=Q.U Z
local notation "P"=> planeP Q.Standard
def Repairs(i:σ):H.Op:= P*F i*P
local notation "v" => Repairs F Q
-- Fog left.Vacc.He
variable (h:Ω∈Q.Standard)(q:∀ i j:σ,Commute (A i j) (planeP Q.Standard))
include h q
omit h q in
lemma stays {V:H.Op}(p:Commute V (planeP Q.Standard))(x:H)(t:x∈Q.Standard): V x∈Q.Standard:= by rw [show V x=P (V x) from (by refine (congrArg (fun y=>V y) (inlet t).symm).trans ?_; exact DFunLike.congr_fun p.eq x)]; exact through _ -- omit
omit q in
lemma traffic_mem : TapeT (Repairs F Q) A R Ω∈Q.Standard := by
 cases R with
 | nil=> exact h
 | cons i R=> cases R with
        | nil=> exact through (U:=Q.Standard) _ -- defeq exterior
        | cons j T=> exact through (U:=Q.Standard) _
-- future point
private def future (i:σ) : List σ → H
 | []=> Ω
 | j::t=> A i j (TapeT (Repairs F Q) A (j::t) Ω)
lemma branches (i:σ)(Z:List σ): future Ω F A Q i Z∈Q.Standard:=by cases Z with
 | nil=> exact h
 | cons j Z=> exact stays Q (q i j) _ (traffic_mem Ω F A (j::Z) Q h) -- tune
-- better produce assignment W F.
include p
lemma titles: ∃ f:σ→ H,(∀ i, f i∈Q.Standard) ∧ ∀ (i:σ)(Z K:List σ), R=K++i::Z→ f i=future Ω F A Q i Z :=by
 classical
 have he (i:σ) : ∃ x:H,x∈Q.Standard ∧ ∀ (Z K:List σ), R=K++i::Z→ x=future Ω F A Q i Z:=by
   by_cases e:i∈R; swap; · exact ⟨Ω,h,fun Z K w=>False.elim (e (by rw [w]; simp))⟩
   obtain ⟨K,S,w⟩:= List.append_of_mem e; refine ⟨future Ω F A Q i S,branches Ω F A Q h q i S,fun Z L E=>congrArg _ ?_⟩
   -- nodup uniqueness, List.append_match
   have he(L T:List σ)(t:R=L++i::T):R.idxOf i=L.length:=by rw [t,List.idxOf_append,if_neg]; simp; exact fun e=>(show (L++i::T).Nodup from t ▸ p).disjoint e (List.mem_cons_self)
   exact (List.cons.inj (List.append_inj_right (w.symm.trans E) ((he K S w).symm.trans (he L Z E)))).2
 choose f hf using he
 exact ⟨f,fun i=>(hf i).1,fun i=>(hf i).2⟩
end
private theorem tassel (x:ℕ→ H)(y:H)(F:ℕ→ H.Op)(z:H)(M:ℝ) (p:Tendsto x atTop (𝓝 y))(h:Tendsto (fun i=>F i y) atTop (𝓝 z))(t:∀ i,‖F i‖≤ M) : Tendsto (fun i=> F i (x i)) atTop (𝓝 z):=by
 let g(i:ℕ):= F i (x i-y); have he:Tendsto g atTop (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero (fun i=> norm_nonneg _) (fun i=> ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (t i) (norm_nonneg (x i-y))))
    convert (Filter.Tendsto.const_mul M (show Tendsto (fun i=>‖x i-y‖) _ (𝓝 0) from (norm_zero (E:=H.space)) ▸ (show Tendsto (fun i=>x i-y) atTop (𝓝 0) from (sub_self y) ▸ p.sub tendsto_const_nhds).norm)) using 1 -- argument order
    rw [mul_zero]
 have hv:= he.add h; rw [zero_add] at hv; exact hv.congr (fun i=> by unfold g; rw [map_sub,sub_add_cancel])
section
variable (Ω: H)(F:σ→H.Op)(A:σ→σ→H.Op)(R:List σ)(p:R.Nodup) (Q:Willow H T)
local notation "P"=> planeP Q.Standard
variable (h:Ω∈Q.Standard)(q:∀ i j:σ,Commute (A i j) (planeP Q.Standard))
include Q
private lemma tall (f:σ→ H) (Z:σ→ ℕ→ Knot T) (v:∀ i:σ, Tendsto (fun k=> (brace (Z i k) Q (F i)) (f i)) atTop (𝓝 (Repairs F Q i (f i)))) (V:∀ i:σ,∀ K L:List σ,R=K++i::L→ f i=future Ω F A Q i L) : Tendsto (fun n=> TapeT (fun i=>brace (Z i n) Q (F i)) A R Ω) atTop (𝓝 (TapeT (Repairs F Q) A R Ω)):=by
 induction R with
 | nil=>exact tendsto_const_nhds
 | cons i S ih=>
    have hp:f i=future Ω F A Q i S:= V i [] S rfl; let Fκ(k:ℕ):= fun i=> brace (Z i k) Q (F i); let z(n):=Fκ n i; have he:= v i; rw [hp] at he; cases S with
    | nil=> exact he
    | cons j l=> let T:=j::l; let x(n:ℕ):=A i j (TapeT (Fκ n) A T Ω); let y:=future Ω F A Q i T
                 exact tassel x y z _ ‖F i‖ (((A i j).continuous.tendsto _).comp (ih (fun j K L e=>V j (i::K) L (by simpa using e)))) he (fun i=>braceC ..)
variable (ν:G)(B:σ→σ→G.Op)(D:σ→G.Op)(S:List σ)(v:S.Nodup)(U:Willow G T)
variable (R':Set (ℂ × ℂ))(r:ℝ) (t:IsClosed R') (u:Convex ℝ R')
include t u p v h q
-- **transport any simultaneous convex price**
lemma quilt (z:0<r) (k:ν∈U.Standard)(l:∀ i j:σ,Commute (B i j) (planeP U.Standard))(w:∀ x:σ→T, (∀ i, ‖x i‖<r)→ relation Ω A R ν B S R' (fun i=> faced Q (F i) (x i)) (fun i=> faced U (D i) (x i))) : relation Ω A R ν B S R' (Repairs F Q) (Repairs D U):=by
 obtain ⟨f,g,y⟩:= titles Ω F A R p Q h q; obtain ⟨f',w',Y⟩:= titles ν D B S v U k l
 choose Z C C₀ C₁ using fun i:σ=>ask_p r Q (f i) (F i) z U (D i) (f' i) (g i) (w' i)
 let TA(n:ℕ):=fun i=>brace (Z i n) Q (F i); let TB(n:ℕ):=fun i=>brace (Z i n) U (D i)
 let a(i:ℕ):=(keep Ω (TA i) A R,keep ν (TB i) B S); apply t.mem_of_tendsto (f:=a) (b:=atTop) (Tendsto.prodMk_nhds (((innerSL ℂ Ω).continuous.tendsto _).comp (tall Ω F A R Q f Z C₀ (fun i K L=> y i L K))) (((innerSL ℂ ν).continuous.tendsto _).comp (tall ν D B S U f' Z C₁ (fun i K L=> Y i L K))))
 exact Eventually.of_forall fun i=> relation_full Ω A R p ν B S v R' u (fun z:T=>‖z‖<r) (fun i=>faced Q (F i)) (fun i=>faced U (D i)) (fun j=>Z j i) (fun _=>0) w (fun j=> C j i) (fun _=> by simpa using z)
#print axioms quilt
end
end YM.CF.Buffered.Afterglow.Hierarchy.Endless.Piper
