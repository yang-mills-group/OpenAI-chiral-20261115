import GaugeFieldConstruction.Crod
import SatinThinTopic
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Roots.Connect
open Function Filter Metric MeasureTheory Finset Mew
open scoped Topology ContDiff BigOperators Matrix
variable {I J K X Y Z E F:Type*}[LinearOrder I][LinearOrder J][LinearOrder K][Fintype I][Fintype J][Fintype K][DecidableEq X][DecidableEq Y][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F] [DecidableEq Z]
variable (σ:I→X)(t:J→X)(C:J→ Key I)(ρ:K→Y)(τ:J→Y)(A:J→Key K)
abbrev Entry (x:X):Finset I:= univ.filter fun i=> σ i=x
abbrev Tours:= ∀ j,Routable (C j) (Entry σ (t j))
-- $ζ C$. key compounds. no costs here.
abbrev SpotQ (C:J→Key I)(v:Key J):= ∑ j,v j • C j
abbrev LegQ (C:J→ Key I)(v:J→ℝ):= SpotQ C fun j=>(v j:ℂ)
lemma Spot_Z : SpotQ C 0=0:=by unfold SpotQ; simp
lemma Leg_Z : LegQ C 0=0:=by unfold LegQ SpotQ; simp
lemma Spot_H (R:J→ℝ)(U:Finset J)(h:Routable (fun j=>(R j:ℂ)) U)(j:J)(p:j∉U)(a:ℝ): LegQ C (update R j a)= LegQ C R+(a:ℂ) • C j:=by
 let T:=univ.erase j; have he(x:J→ℝ):LegQ C x=(x j:ℂ) • C j+∑ i∈T,(x i:ℂ) • C i:=(add_sum_erase _ (fun i=>(x i:ℂ) • C i) (mem_univ _)).symm
 rw [he,he,show (R j:ℂ)=0 from h j p, zero_smul, zero_add, update_self,add_comm]; apply congrArg (fun x: Key I=>x+(a:ℂ) • C j); apply sum_congr rfl; intro i t; rw [update_of_ne (mem_erase.mp t).1]
lemma Turn_R : Continuous (LegQ C):= continuous_finsetSum _ (fun j _=> (Complex.continuous_ofReal.comp (continuous_apply j)).smul continuous_const)
abbrev Routs (l:List J)(x:J→ℝ):= ∀ i:J,i∉l→x i=0
lemma outside_j {j:J}{l:List J}{x:J→ℝ}(u:Tours σ t C)(r:Routs l x)(z:(List.map t (j::l)).Nodup): ∀ i∈Entry σ (t j),LegQ C x i=0:=by
 intro i p; unfold LegQ SpotQ; rw [Finset.sum_apply]; apply sum_eq_zero; intro k g; by_cases f:k∈l
 · have hp:t j∉ l.map t:= (List.nodup_cons.mp (show (t j :: _).Nodup from z)).1
   change ((x k:ℝ):ℂ)*C k i=0; rw [u k i (fun h=>hp ((List.mem_map.mpr ⟨k,f,(mem_filter.mp h).2.symm.trans (mem_filter.mp p).2⟩))), mul_zero] -- tune
 change ((x k:ℝ):ℂ)*C k i=0; rw [r k f, Complex.ofReal_zero, zero_mul]
-- mask increments
variable {f:Key I→E}(p:River f)
abbrev Jetd (H:List I→E) : List J→E:= aux H where
 aux (H:List I→E): List J→E
 | []=>H []
 | j::t'=>∑ i∈ Entry σ (t j), C j i • aux (fun k=> H (i::k)) t'
abbrev Pica (f:Key I→E): List J→E:=Jetd σ t C (tipI f)
abbrev DataU (f:Key I→E)(j:J)(z:Key I):=∑ i∈ Entry σ (t j), C j i • cutI f i z
lemma Data_h (j:J)(p:River f):River (DataU σ t C f j) := (tip_bank _ _ (fun i _=> River.scale (p.flow _) _)).1
lemma Jet_add (u v:List I→E)(l:List J): Jetd σ t C (fun i=>u i+v i) l=Jetd σ t C u l+Jetd σ t C v l:=by
 induction l generalizing u v with
 | nil=> simp [Jetd,Jetd.aux]
 | cons j l ih=> rw [Jetd,Jetd,Jetd, Jetd.aux,Jetd.aux,Jetd.aux, ←sum_add_distrib]; refine sum_congr rfl fun i w=>?_ ; exact (congrArg (C j i • ·) (ih (fun s=>u (i::s)) (fun s=>v (i::s)))).trans (smul_add ..)
lemma Jet_scale(a:ℂ)(u:List I→E)(l:List J): Jetd σ t C (fun i=>a • u i) l=a • Jetd σ t C u l:=by
 induction l generalizing u with
 | nil=> simp [Jetd,Jetd.aux]
 | cons j l ih=> rw [Jetd,Jetd,Jetd.aux,Jetd.aux,smul_sum]; apply sum_congr rfl; intro i _; exact (congrArg (C j i • ·) (ih fun x=>u (i::x))).trans (smul_comm ..)
lemma Jet_zero(l:List J): Jetd σ t C (fun _=>(0:E)) l=0:=by have ht:=Jet_scale (E:=E) σ t C 0 (fun _=>0) l; simpa only [zero_smul] using ht
lemma Jet_sum{P:Type*}(U:P→ List I→E)(s:Finset P)(l:List J): Jetd σ t C (fun i=> ∑ j∈s,U j i) l=∑ j∈s,Jetd σ t C (U j) l:=by
 classical
 induction s using Finset.induction_on with
 | empty=> simpa only [sum_empty] using Jet_zero (E:=E) σ t C l
 | insert i s h ih=> simp_rw [sum_insert h,Jet_add (v:=fun x=>∑ j∈s,U j x)]; rw [ih] -- tune
lemma S_d (p:River f)(j:J)(l:List J): Pica σ t C (DataU σ t C f j) l=Pica σ t C f (j::l):=by
 let i'(i:I)(x:Key I):= C j i • cutI f i x; rw [Pica,show tipI (DataU σ t C f j) =(fun L=>∑ i∈Entry σ (t j), C j i • tipI f (i::L)) from ?_, Jet_sum σ t C (fun i L=>C j i • tipI f (i::L))]; · simp_rw [Jet_scale σ t C _ (fun x=>tipI f (_::x))]; rw [Pica,Jetd,Jetd.aux]
 funext x; exact ((tip_bank (Entry σ (t j)) i' (fun i _=> River.scale (p.flow i) _)).2 x).trans (sum_congr rfl fun i _=> tip_C (p.flow i) (C j i) x)
variable {g:Key K→F}(h:River g)
variable [NormedSpace ℝ E][NormedSpace ℝ F][IsScalarTower ℝ ℂ E][IsScalarTower ℝ ℂ F]
variable (S:E→L[ℝ] F)(u:Tours σ t C)(e:Tours ρ τ A)
include p u
lemma lineS (l:List J)(j:J)(x:J→ℝ)(v:Routs l x)(k:ψS t (j::l))(w:LegQ C x ∈ hill I): HasDerivAt (fun i:ℝ=> f (LegQ C (update x j i))) (DataU σ t C f j (LegQ C x)) 0:=by
 let U:=Entry σ (t j); have hp:=crept p w (u j) (outside_j σ t C u v k)
 let D(x:ℝ):ℂ:=x; have hl: D 0=0:=Complex.ofReal_zero; have he:= (show HasDerivAt _ _ (D 0) from hl.symm ▸ hp); have hg: HasDerivAt D (1:ℂ) (0:ℝ):=Complex.ofRealCLM.hasFDerivAt.hasDerivAt
 have ht(y:ℝ):LegQ C (update x j y)=LegQ C x+(y:ℂ) • C j:= Spot_H C x l.toFinset (fun i q=>by change (x i:ℂ)=0; rw [v i (by simpa using q),Complex.ofReal_zero]) j (by simpa using (List.nodup_cons.mp (uS_b t k)).1) y
 simp_rw [ht]; exact (he.scomp 0 hg).congr_deriv (one_smul ..)
include e h
lemma Darboux {l:List J}(he:ψS t l)(ht:ψS τ l) (Y:∀ᶠ x:J→ℝ in 𝓝 0, Routs l x → g (LegQ A x)=S (f (LegQ C x))) : Pica ρ τ A g l= S (Pica σ t C f l):=by
 induction l generalizing f g
 case nil=>
    have h:= mem_of_mem_nhds Y (show Routs [] (0:J→ℝ) from fun _ _=>rfl); rw [Leg_Z,Leg_Z] at h; unfold Pica Jetd; rw [Jetd.aux,Jetd.aux]; exact h
 case cons i l ih=>
    have hz:ψS t l:= (List.nodup_cons.mp he).2; have hv:ψS τ l:=(List.nodup_cons.mp ht).2
    rw [← S_d σ t C p,←S_d _ _ _ h]; apply ih (Data_h _ _ _ _ p) (Data_h _ _ _ _ h) hz hv -- auto included order
    have hU : ∀ᶠ x in 𝓝 (0:J→ℝ), LegQ C x ∈ hill I:= by have hx: Tendsto (LegQ C) (𝓝 0) (𝓝 0):= Leg_Z C ▸ (Turn_R C).continuousAt (x:=0); exact hx.eventually (closedBall_mem_nhds _ zero_lt_one)
    have hW : ∀ᶠ x in 𝓝 (0:J→ℝ), LegQ A x ∈ hill K:= by have hx: Tendsto (LegQ A) (𝓝 0) (𝓝 0):= Leg_Z A ▸ (Turn_R A).continuousAt (x:=0); exact hx.eventually (closedBall_mem_nhds _ zero_lt_one)
    obtain ⟨V,wP,b,v⟩:= _root_.mem_nhds_iff.mp Y
    filter_upwards [hU,hW,b.mem_nhds v] with x m n o; intro k
    let H':=congrArg (fun a=>update x i a) (k i (List.nodup_cons.mp (uS_b _ he)).1)
    have hc: Continuous (fun y:ℝ=>update x i y):=(continuous_update (A:=fun _:J=>ℝ) i).comp (continuous_const.prodMk continuous_id)
    let X:=fun y:ℝ=>g (LegQ A (update x i y)); let Y':=fun y:ℝ=> S (f (LegQ C (update x i y)))
    have hT:X=ᶠ[𝓝 0] Y':=by
       filter_upwards [(hc.continuousAt (x:=0)).tendsto.eventually (b.mem_nhds (show update x i 0∈V from by rw [←H',update_eq_self]; exact o))] with y h; refine wP h ?_
       intro j q; obtain ⟨u',v'⟩:=show j≠i∧j∉l by simpa using q
       exact (update_of_ne u' ..).trans (k j v')
    exact ((lineS ρ τ A h e l i x k ht n).congr_of_eventuallyEq hT.symm).unique (S.hasFDerivAt.comp_hasDerivAt 0 (lineS σ t C p u l i x k he m))
#print axioms Darboux
end YM.CF.Roots.Connect
end
