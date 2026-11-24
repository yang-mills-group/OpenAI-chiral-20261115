import YM.CF.Spark.Shank
import YM.CF.Emu.Well
/-!
# New finite regulator synergy theorem. Reflection positive + SAME chiral
reindex tested covariance limits. USA—all stated explicitly for single field.

**Not** interacting QFT construction. The cap and temperatures in this sanity
test are *not* a running coupling trajectory. Heat expansion estimates initially
volume/wind safe (see `Paige`, `Reed`, etc.); here extra-time scheduling to bound
open amplitudes. Cone phase choice consistent and explicit in Vial and luggage.
RP for tested glazes, no claims on rank of interacting transfer or even
rotational covariance beyond what's in formal conditions. Chiral limit claimed
here is position-space free detector Wilson/C-charge weak-field band with
transported group anchored color frames for inserts across generations (no
projection/replacement before reading). Does not establish same under continuum
AF scales, exclusion in limiting OS spaces, or Ward running / quantum anomaly
claims in an interacting theory. This is a finite-volume theorem plus a
particular UV/free/current probe.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Phase.Sample Branch MeasureTheory RG Wilson WilsonStartup RP Nova Kea Ave Fock SU CF.Jet Broc Petal Spire Scroll Peaks Pastry Pic Sods Paige Vault Graph Dial Brace Mint Bloch Fir Ember Onyx Emu
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {L B m N: Side}{e H a b c d v σ h Y w r l t τ C S β:ℝ}{i j k n:ℕ}{O:Odd L.val}{T:Pricing j L O (Thread j)}{P:Grasp T B e}{V:Pearl P}{f:ℕ→Side}(F: Pic.Span V H b v c a r n)(R:Reg 0 e B)(Z:Vial P R l Y h C d)
local notation "n'"=>Domain m B
local notation "U'"=>Briar m B e
local notation "E'"=>Elf m B
local notation "M'"=>CSide m B
local notation "NN"=>aj B f
local notation "A'"=> Greek
variable {α:Type*}
lemma frozen (g:Geometry M')(f:FC (Single M')) : crossL (helix M').symm (twist (quantU (tradew _ g)) f)= twist (RP.colorW (m:=m) (B:=B) g) (crossL (helix M').symm f) :=by
 let N:=M'; let A:= conjG matter (g ∘ node (N:=N)); let W:=quantU (tradew N g); let E:= (helix N).symm; let U:=quantU A; change crossL E (twist W f)= twist U (crossL E f)
 have he:portW (helix N).symm A.val=(tradew N g).val:=by
   unfold portW A; ext ⟨⟨i,b⟩,v⟩ ⟨⟨j,c⟩,k⟩; by_cases h:i=j<;>by_cases e:b=c<;> simp [h,e,conjG,tradew,jump_apply, helix, Lat.color] <;> first| rfl|simp
 have ht: crossL E W.val=U.val:=by
    refine cx_eq E _ _ (fun p=>?_); let F:= E.toEmbedding; have hp:= freezes F ∅ (shelfG E) A.val p; rw [show addS F ∅ A.val= (tradew N g).val from (flexL E _).trans he] at hp; exact hp
 have hp: crossL E (star W.val)=star U.val:=by
    have hf: U.val*crossL E (star W.val)=1:=by rw [←ht,←cx_m,W.property.2]; refine cx_eq _ _ _ fun x=>by rw [act_one,act_one]
    calc _ = star U.val * (U.val * crossL E (star W.val)):=by rw [←mul_assoc,U.property.1,one_mul]
         _ = _:=by rw [hf,mul_one]
 rw [twist_formula,twist_formula,cx_m,cx_m,ht,hp]
lemma dart_g (W:Opt (α:=α) (CSide m B))(p:Geometry M'): rideG m B p (dart W)=dart W:=by
 funext x; unfold RP.rideG dart seekV; unfold nextG; simp only [teen]; rw [frozen,twist_inv]
open Reed (Fine)
lemma dart_f (W:Opt (α:=α) (CSide m B))(x:Pack m B): Fine (upperP M') univ (knotS W.L) (dart W x):=by
 let N:= M'; let U:= (helix N).symm
 have hs(A B:FC (Single N)): crossL U (A+B)=crossL U A + crossL U B:=cx_eq U (A+B) _ fun x=>by rw [act_add,act_add,←crossed,←crossed]; exact map_add (Fock.hoist U.toEmbedding ∅) _ _
 have hL(a:ℂ)(A:FC (Single N)):crossL U (a • A)= a • crossL U A:=cx_eq U _ _ fun x=>by rw [act_smul,act_smul,carts_s,crossed]
 have he{b: Bool}{A:FC (Single N)}(q:Fine (halfS N) univ b A):Fine (upperP N) univ b (crossL U A):=by
    induction q with
    | empty=> rw [show crossL U (0:FC (Single N))=0 from cx_eq _ _ _ fun x=>by simp [cartsL]]; exact Fine.empty _
    | one=> rw [show crossL U (1:FC (Single N))=1 from cx_eq _ _ _ fun x=>by rw [act_one,act_one]]; exact Fine.one
    | seed i _=>
       obtain ⟨j,rfl⟩:=U.surjective i; have he:U j∈halfS N ↔ j∈upperP N:=by simp [U,helix, halfS, upperP]
       have hp:crossL U ((Reed.think (halfS N)).term (U j))=(Reed.think (upperP N)).term j:=by
          change crossL U (if U j∈_ then _ else _) = if j∈_ then _ else _; simp only [he]; split_ifs with h; exact (cx_p ..).1
          have hx:= hL (-1) (takeF (U j)); rw [(cx_p ..).2] at hx; simpa using hx
       rw [hp]; exact Fine.seed j (mem_univ _)
    | grow _ _ ih hi=>rw [cx_m]; exact Fine.grow ih hi
    | add _ _ ih hi=>rw [hs]; exact Fine.add ih hi
    | scale _ c ih=>rw [hL]; exact Fine.scale ih _
 exact he (paw_f W.o x.1 W.R W.f W.L)
variable (q:Clip)
def elixir(m:Side)(u t:ℝ)(x:RP.Test m B):= shire q u t R (scarf m) x / shire q u t R (scarf m) (emptyF m B)
structure LegalR (m:Side)(u t:ℝ):Prop where
 funds:0 < shire q u t R (scarf m) (emptyF m B)
 normal: elixir R q m u t (emptyF m B)=1
 gauge (x g):elixir R q m u t (rideG m B g x)=elixir R q m u t x
 mirror (i b W l) (T:OfferedF m B i W b): 0≤ elixir R q m u t (squareR m B l (R.c m) i W b)
include Z F
lemma potion (hl:0<h)(hv:0<d)(hd:d<1)(f:ℕ→Side)(g:Tendsto (bean f) atTop atTop): ∃ A:ℕ→ℝ,(∀ᶠ i in atTop,0<A i) ∧ ∀ U S:ℕ→ℝ,(∀ᶠ i in atTop,0 <S i ∧ S i ≤ A i)→(∀ᶠ i in atTop,LegalR R q (f i) (S i) (U i))∧∀ (α:Type _) (z:ℕ→ℝ)(M:Plot α z)(P:Yard (aj B f) z)(o:∀ i,Site (aj B f i))(D:List α), Tendsto (fun i=> elixir R q (f i) (S i) (U i) (dart (Opt.mk (o i) (z i) D (M.pal i)))) atTop (𝓝 (runes M.rho D)):=by
 obtain ⟨K,A,τ,W,hP,h,h'⟩:=shaft F R Z g hl; refine ⟨W,h'.mono fun i k=>k.2,fun U S b'=>?_⟩; have ht:= ((h'.mono fun i k=>k.1).and b'); constructor
 · have hx:0<b/(2*poseX)/2:=by have ht:= F.pos; have hu:=pose_p; positivity
   filter_upwards [(pillar F R Z g hl hv hd hP q U S ht).1] with i ⟨u',k,v,x⟩; let Y:=shire q (S i) (U i) R (scarf (f i)) (emptyF (f i) B)
   have he: Y ≠0:=by intro h; unfold rive airt at x; rw [dart_nil,show shire _ _ _ _ _ _= 0 from h, mul_zero,norm_zero] at x; exact not_le.mpr (mul_pos u' hx) x
   refine ⟨lt_of_le_of_ne v he.symm,div_self he,fun x g=>?_ ,fun i b W l g=> div_nonneg ?_ v⟩
   · unfold elixir; rw [warp _ _ _ _ _ _ Z.valid.bond.passesP]
   exact greenR q _ _ _ _ _ Z.valid.bond.passesP _ _ _ g
 intro T z M Y o D; exact ports F R Z g hl hv hd hP q U S ht z h M D Y o -- ambiguity
omit Z F
lemma fromY {y:ℕ→ℝ}(h:Yard (aj B f) y): Tendsto (bean f) atTop atTop:=by
 have he:=roam_n h; let S:ℝ:= 2*B.val; have hp:0<S:= by unfold S; have hh:B.val>0:=B.property; positivity
 refine (he.atTop_mul_const (inv_pos.mpr hp)).congr fun i=>?_ ; change Greek _ * S⁻¹=_; unfold Greek bean S aj; change (((f i).val*2*B.val:ℕ):ℝ)*_= _; push_cast; field_simp
lemma garnish(L:Side)(p:Odd L.val)(j:ℕ)(hp:1≤j)(g:Even j)(h:ℝ)(y:0<h):∃ (V: Pricing j L p (Thread j))(B:Side)(e:ℝ)(P:Grasp V B e)(Q:Pearl P)(H b v c a r:ℝ)(n:ℕ), Nonempty (Pic.Span Q H b v c a r n)∧∃ σ l C Y:ℝ,0<σ∧σ<1∧ ∀ k:ℝ,0<k → ∃ R: Reg 0 e B,1-k<R.knob∧ Vial P R l Y h C σ:=by
 obtain ⟨Y,hY⟩:= sparkling g hp p; obtain ⟨R⟩:=Acorn.restoreX j hp; obtain ⟨n,v⟩:= ava Y R hp; let b:Side:=⟨n+1,by positivity⟩; obtain ⟨l,Q⟩:=v b (Nat.le_add_right n _); let D:Side:= ⟨l+1,by positivity⟩; obtain ⟨K,X⟩:=Q D (Nat.le_add_right ..)
 obtain ⟨σ,H,hX,k,U⟩:= Reed.FiniteK h y
 let A:Side:=⟨max K k+1,by positivity⟩; let B:= b*(D*A); have he:max K k≤B.val:=le_trans (Nat.le_add_right (max K k) 1) ((Nat.le_mul_of_pos_left A.val D.property).trans (Nat.le_mul_of_pos_left _ b.property)); obtain ⟨e,G,Q⟩:= X B ((le_max_left ..).trans he) ⟨_,rfl⟩ ⟨b*A, by unfold B; ac_rfl⟩
 obtain ⟨ε,Y',p',L',h',pH,P⟩:= U B ((le_max_right ..).trans he); let r:=min ε e; have hw:0<r:=lt_min h' G
 obtain ⟨F,⟨V⟩,W⟩:=Q r hw (min_le_right ..); obtain ⟨f,g⟩:= P r hw (min_le_left ..); obtain ⟨u,v,x,z,a,r',n,T⟩:=crop0 V hY hp hw; refine ⟨Y,B,r,F,V,u,v,x,z,a,r',n,T,σ,p',L',Y',H,hX,fun o h=>?_⟩; obtain ⟨R,p,U,C⟩:= g 0 o h; exact ⟨R,p,capperL F hw U C⟩
end YM.CF.Spark
