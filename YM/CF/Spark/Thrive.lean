import YM.CF.Spark.Louv
import YM.CF.Emu.Pit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Phase.Sample Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova Kea Ave Fock SU CF.Jet Broc Petal Spire Scroll Peaks Pastry Pic Sods Paige Vault
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B m N: Side}{e H a b c d v σ h Y:ℝ}{i j n:ℕ}{O:Odd L.val}{T:Pricing j L O (Thread j)}{P:Grasp T B e}
local notation "n'"=>Domain m B
local notation "U'"=>Briar m B e
def tiltK(x:U' × U'):= ∑ l:Edge (Site n'), Cube.cmp firstF (x.1.val l) (x.2.val l)
lemma throb (f:Briar m B e→ℂ)(h:Continuous f) (u:ℝ)(p:0<u):∃ v:ℝ,0<v ∧ ∀ U V:Briar m B e,lawnK U.val V.val v → ‖f U-f V‖ ≤u:=by
 let X:Set (U' × U'):= {x | u ≤ ‖f x.1-f x.2‖}; have he:IsCompact X:= (isClosed_le continuous_const (((h.comp continuous_fst).sub (h.comp continuous_snd)).norm)).isCompact; by_cases k:X.Nonempty
 · let A:=tiltK (m:=m) (B:=B) (e:=e); have hx:Continuous A:= continuous_finsetSum _ fun i _=> ((SU.fund_cont.comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))).sub (SU.fund_cont.comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))).norm
   obtain ⟨y,w,l⟩:=he.exists_isMinOn k hx.continuousOn; have hX: 0<A y:=by
      by_contra hv; have ht:A y ≤0:= not_lt.mp hv
      have hy:y.1=y.2:=by
         apply Subtype.ext; funext i; have hz:Cube.cmp firstF (y.1.val i) (y.2.val i)≤ 0:= (single_le_sum (f:=fun k=>Cube.cmp firstF (y.1.val k) (y.2.val k)) (fun _ _=>norm_nonneg _) (mem_univ i)).trans ht
         apply Subtype.ext; apply Subtype.ext; exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)
      change u≤ ‖f y.1-f y.2‖ at w; rw [hy,sub_self,norm_zero] at w; exact p.not_ge w
   let s:ℝ:= Fintype.card (Edge (Site n')); have hp:0<s:=by unfold s; positivity
   let r:=A y/s/2; refine ⟨r,by unfold r; positivity,fun x y' t=>le_of_not_gt ?_⟩; intro ha; apply lt_irrefl (A y); have hy:= l (a:=(x,y')) (show (x,y')∈X from ha.le); change A y ≤ A (x,y') at hy; refine lt_of_le_of_lt hy (lt_of_le_of_lt (sum_le_sum (fun k _=> t k)) ?_); rw [sum_const,card_univ,nsmul_eq_mul]; change s*r<A y; unfold r; field_simp; nlinarith
 exact ⟨1,zero_lt_one,fun x y _=> le_of_not_gt (fun v=> k ⟨(x,y),v.le⟩)⟩
variable (p:0 ≤e)
abbrev rollerU(a:ℝ)(D C:ℝ)(m: Side) :ℝ:= Real.exp (-a*(m.val:ℝ))*(2*(D*C))
def Horizontal (c:ℝ)(f:Briar m B e→ℂ)(p:0 ≤ e):Prop:= Continuous f ∧ (∀ x:Briar m B e,∀ g: Court m B,f (routeS g x)=f x) ∧ ∀ z, ‖f (pole m B p z)- f (pole m B p slate)‖ ≤ c
lemma saved (g:Briar m B e→ℂ)(f: Seal (Index m)→U'→ℂ)(w:Seal (Index m)→ℝ)(hp:Charge (moneyW m B e) (terr _) a c f w)(k:0<a)(q:∀ x,g x=∑ i,f i x)(u:4≤ m.val):Horizontal (rollerU a (Fintype.card (Index m)) c m) g p:=by
 constructor; · rw [funext q]; exact continuous_finsetSum _ fun i _=> (hp.pledge i).ct
 refine ⟨fun x t=>?_,fun z=>?_⟩
 · rw [q,q]; apply sum_congr rfl; intro i _; exact ((hp.pledge i).dress t x).symm
 rw [q,q]; exact faultX _ (fun i=>f i _) (fun i=>f i _) _ hp.rankV (fun i=>(hp.pledge i).price) (fun i u=> gspan ((hp.pledge i).shape u)) k (fun i=>(hp.pledge i).owns _) (fun i=>(hp.pledge i).owns _) (fun i t l=>pupil z i _ _ p (hp.pledge _) t l u)
lemma gone (g:Briar m B e→ℂ)(h:Screen (soar m B e) (aether n 1 e m B) n g a c)(k:0<a)(u:4≤ m.val):Horizontal (rollerU a (Fintype.card (Site n')) c m) g p:=by
 obtain ⟨f,w,hp,H,h⟩:=h; constructor; · rw [funext h]; exact continuous_finsetSum _ fun i _=> (hp i).cont
 refine ⟨fun x t=>?_,fun z=>?_⟩
 · rw [h,h]; apply sum_congr rfl; intro i _; exact (hp i).gauge x t
 rw [h,h]; exact faultX _ (fun i=>f i _) (fun i=>f i _) _ H (fun i=>(hp i).pos) (fun i u=> gspan ((hp i).travel u)) k (fun i=>(hp i).sumline _) (fun i=>(hp i).sumline _) (fun i t l=>tune_f z i _ _ p (hp _).toPeak t l u)
lemma more_h {F G:Briar m B e→ℂ}(X:Horizontal a F p)(Y:Horizontal b G p):Horizontal (a+b) (fun x=>F x+G x) p:=⟨X.1.add Y.1,fun x t=>congrArg₂ HAdd.hAdd (X.2.1 x t) (Y.2.1 x t),fun i=> by dsimp only; rw [add_sub_add_comm]; apply (norm_add_le ..).trans (add_le_add (X.2.2 _) (Y.2.2 _))⟩
lemma mult_h {F:Briar m B e→ℂ}(X:Horizontal a F p)(t:ℝ)(h:0≤t):Horizontal (t*a) (fun x=>(t:ℂ)*F x) p:=by refine ⟨continuous_const.mul X.1,fun x t=>congrArg _ (X.2.1 ..),fun i=>?_⟩; dsimp only; rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg h]; exact mul_le_mul_of_nonneg_left (X.2.2 _) h
variable {s:1≤H}(R:Reg 0 e B){w: Seal (Index m)→ℝ}(K:Seal (Index m)→Briar m B e→ Ewe m B)
def amen (P:Grasp T B e)(i:ℕ)(x:U') :ℂ:= scalarD K x+ (R.time i:ℂ)*energ m B (R.c m) x.val + candle m B (P.cost m Brace.firstM) x.val
abbrev lid (m B: Side)(h a i C y:ℝ):ℝ:= rollerU (h/2) (Fintype.card (Index m)) (Petal.bulk h 16*(1/3)) m+i*rollerU h (Fintype.card (Index m)) y m+rollerU a (Fintype.card (Site (Domain m B))) C m
lemma star_h (Mh:Screen (soar m B e) (aether 0 1 e m B) 0 (fun x:Briar m B e=> candle m B (P.cost m Brace.firstM) x.val) a c)(hq:0<a)(hl:0<h)(U:Warranty B e 0 h σ P.baseY Y R)(hp:Effect s m B e 0 R i h σ K w P.baseY)(u:4≤ m.val):Horizontal (lid m B h a (R.time i) c Y) (amen R K P i) p:=by
 let X:=fun x:Briar m B e=> energ m B (R.c m) x.val; let Z:= scalarD K; obtain ⟨f,q,hz,l⟩:= (U.payroll m).paysT; have he:= mult_h p (saved p X _ q hz hl l u) (R.time i) ((Nat.cast_nonneg i).trans (R.charges i).1.le); let D:=fun x:Briar m B e=>candle m B (P.cost m Brace.firstM) x.val; have ht:=gone p D Mh hq u; exact more_h p (more_h p (saved p Z _ w hp.scalar (half_pos hl) (fun _=>rfl) u) he) ht
end YM.CF.Spark
