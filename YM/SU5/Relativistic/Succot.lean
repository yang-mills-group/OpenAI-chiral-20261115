import YM.SU5.Relativistic.Nero
/-! # Alphabet for entire physical calibration. NO coefficients depend on M. no covariance required until feeding painted Receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 290000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Lifted BPress.Spin.Blank
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {K:Calibration}
structure Wine where
 fees : LinksC→ℂ
 song : List Bite
def pulseX (N:Side) (w:Wine) (U:Pane N):= w.fees (onC N U) • chartP N w.song
variable (K:Calibration)
abbrev motet (N:Side) (L:List Wine) : Mark N:=fun x=> ((L.map fun w=>pulseX N w x.1)).sum
def dek(L:List Wine): Buffered.Family K :=fun m=> motet (K.c m) L
def tallyW (L:List Wine):= (L.map fun w=> w.fees 1*zTariff w.song).sum
def realPay {N:Side}(k:ℕ)(M:Jill.Male)(L:List Wine) :ℂ:= (L.map fun w=>w.fees 1 * earnK (N:=N) M k w.song).sum
lemma weakRatio {N:Side}(k:ℕ)(M:Jill.Male)(p:IsStarProjection (spar 4 M (1:Pane N)))(L:List Wine)(v:Wave (Single N))(h:Sea (spar 4 M 1) v): inner ℂ v (acts ((Saber (B:=tickA N) p k).glow (motet N L (1,1))) v)=realPay (N:=N) k M L:=by
 induction L with| nil=>simp [motet,Shaft.glow_zero,realPay]| cons i L ih=>
    unfold motet realPay pulseX at *; rw [List.map_cons,List.sum_cons,Shaft.glow_sum,act_add,inner_add_right]; rw [ih,List.map_cons,List.sum_cons, Shaft.glow_free,act_smul,inner_smul_right]; rw [bandN k _ p v h]; simp only; rw [show onC N (1:Pane N)=1 from funext (fun x=> onC_spec ..)] -- tune
lemma warmRatio (L:List Wine)(ε:ℝ)(e:0<ε):∀ᶠ k:ℕ in atTop,∃ n:ℕ,∀ (S:Side)(M:Jill.Male),n≤ S.val→n≤ M.val.val→Even S.val→ IsStarProjection (spar 4 M (1:Pane S))→ ‖realPay (N:=S) k M L-tallyW L‖≤ε:=by
 induction L generalizing ε with
 | nil=> filter_upwards with n; refine ⟨0,fun a b _ _ _ _=>?_⟩; simpa [realPay,tallyW] using e.le
 | cons i L ih=>
    let y:=‖i.fees 1‖+1; have hy:0<y:=by unfold y; positivity
    let v:= ε/(2*y); have hv:0<v:=by unfold v; positivity
    filter_upwards [gift i.song v hv,ih (ε/2) (half_pos e)] with k u w
    obtain ⟨p,u⟩:=u; obtain ⟨q,w⟩:=w; refine ⟨max p q, fun S M g l a h=>?_⟩; simp only [realPay,tallyW,List.map_cons,List.sum_cons]; let P:=realPay (N:=S) k M; let x:= i.fees 1
    change ‖x*earnK (N:=S) M k i.song+P L-(x*zTariff i.song+tallyW L)‖≤ε; rw [show x* _+P L-(_+tallyW L)=x*(earnK (N:=S) M k i.song-zTariff i.song)+(P L-tallyW L) from (?_)]; swap; · ring
    apply (norm_add_le ..).trans; rw [norm_mul]; apply (add_le_add (mul_le_mul (show ‖x‖≤y from le_add_of_nonneg_right zero_le_one) (u _ (by omega) a _ (by omega) h) (norm_nonneg _) hy.le) (w S M (by omega) (by omega) a h)).trans_eq; unfold v; field_simp; norm_num
variable {K} {S:Finset Cover} {F:Buffered.Family K}
def label: List Bite→Bool| []=>false| _::L=>!(label L)
lemma label_append(a b:List Bite): label (a++b)=(label a).xor (label b):=by induction a with| nil=> simp [label]| cons i a ih=> rw [List.cons_append,label,label,ih]; cases h:label a<;>cases g:label b<;>rfl
structure Winery (p:Bool)(S:Finset Cover)(A:Wine):Prop where
 price : Continuous A.fees
 near (U V:LinksC)(h:Agrees S U V): A.fees U=A.fees V
 ethic : label A.song=p
 sewn(i:Bite)(h:i∈ A.song): nodeC i.root ∈ S
abbrev AreaW (p:Bool)(S: Finset Cover)(A:List Wine):=∀ i∈A, Winery p S i
def hasPhase (p : Bool) (S: Finset Cover) (F:Buffered.Family K) := ∃ L:List Wine, AreaW p S L∧F=dek K L
lemma recipe {p:Bool} (u:InTest K false S p F) : hasPhase p S F:=by
 let v:LinksC→ ℂ:= fun _=>1
 induction u with
 | seed s=>
   obtain ⟨g,h,w⟩:=s.narrow (by simp); let A:Wine:=⟨g,[]⟩
   refine ⟨[A],?_,?_⟩; · intro i p; rw [(List.mem_singleton.mp p)]; exact ⟨h,fun U V e=>(by have h:= s.locus (U,1) (V,1) e (fun _ _ _=>rfl); rw [w] at h; exact h),rfl,fun i h=>by simp [A] at h⟩
   funext m x; simp [scalar, w,dek,motet,pulseX, A,chartP]
 | @creator x i b u t=>
   let A:Wine:=⟨v,[⟨x,i,b,false⟩]⟩; refine ⟨[A],fun i p=>?_ ,?_⟩
   · rw [List.mem_singleton.mp p]; refine ⟨continuous_const,fun _ _ _=>rfl,rfl,fun i h=>(List.mem_singleton.mp h) ▸ t⟩
   funext m y; simp [creation,dek,motet,pulseX,A,v,chartP,vix,Bite.loc,creed]
 | @remover x i b u t=>
   let A:Wine:=⟨v,[⟨x,i,b,true⟩]⟩; refine ⟨[A],fun i p=>?_ ,?_⟩
   · rw [List.mem_singleton.mp p]; exact ⟨continuous_const,fun _ _ _=>rfl,rfl,fun i h=>(List.mem_singleton.mp h) ▸ t⟩
   funext m y; simp [removal,dek,motet,pulseX,A,v,chartP,vix,Bite.loc,creed]
 | @zero b=> exact ⟨[],fun i p=>by simp at p,(by funext m x; simp [dek,motet])⟩
 | one=>
   let A:Wine:=⟨v,[]⟩; refine ⟨[A],fun i p=>(List.mem_singleton.mp p) ▸ (show Winery false S A from ⟨continuous_const,fun _ _ _=>rfl,rfl,fun i h=>by simp [A] at h⟩),?_⟩; funext m x; simp [dek,motet,pulseX,A,v,chartP]
 | add _ _ a b=>
   obtain ⟨P,t,rfl⟩:= a; obtain ⟨B,b,rfl⟩:= b; exact ⟨P++B, fun i h=>(List.mem_append.mp h).elim (t i) (b i), by funext m x; simp [dek,motet]⟩
 | @smul X p k t a=>
   obtain ⟨P,x,rfl⟩:=a; let A(s:Wine):Wine:=⟨k • s.fees,s.song⟩
   refine ⟨P.map A,fun i p=>?_,?_⟩
   · obtain ⟨i,v,rfl⟩:= List.mem_map.mp p; obtain ⟨h,t,g,e⟩:=x i v; exact ⟨continuous_const.smul h,fun i j p=> congrArg (k • ·) (t i j p),g,e⟩
   funext m x; change k • (dek K P m x)=_; simp only [dek,motet,List.map_map,pulseX]; rw [List.smul_sum]; congr 1; simp [List.map_map,A,Function.comp_def,mul_smul]
 | @mul X Y b c l k h w=>
   obtain ⟨U,Z,rfl⟩:=h; obtain ⟨V,D,rfl⟩:=w; let A(x y:Wine):Wine:=⟨x.fees*y.fees,x.song++y.song⟩
   refine ⟨U.flatMap (fun i=> V.map (A i)),fun i p=>?_,?_⟩
   · obtain ⟨j,g,p⟩:=List.mem_flatMap.mp p; obtain ⟨l,k,rfl⟩:=List.mem_map.mp p; obtain ⟨h,w,q,e⟩:=Z j g; obtain ⟨y,a,t,f⟩:=D l k; exact ⟨h.mul y,fun i j p=>congrArg₂ (· * ·) (w i j p) (a i j p),by unfold A; rw [label_append,q,t],fun i h=>(List.mem_append.mp h).elim (e i) (f i)⟩
   funext m x; change motet _ U x*motet _ V x=motet _ _ x; clear l k Z D
   induction U with| nil=>simp [motet]| cons a L ih=>
     unfold motet at *; simp only [List.flatMap_cons,List.map_cons,List.sum_cons,List.map_append,List.sum_append,add_mul]; rw [ih]; congr 1; clear ih; induction V with| nil=>simp| cons i V ih=> simp only [List.map_cons,List.sum_cons]; rw [mul_add,ih]; congr 1; simp only [A,pulseX,chartP,List.map_append,List.prod_append,Pi.mul_apply,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; ring_nf
end YM.CF.Papyrus.Franc.Loaves
