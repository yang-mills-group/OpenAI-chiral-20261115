import YM.CF.Broc.Cusp
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B:Side}{j l b n:ℕ}{e p d a w:ℝ} (H:CoinG j l b n d a w)(ha:0<a)(hw:0<w)(G:Guide B e p d)(he:b≤(CSide m B).val)(M:Male)
include H G he
def rateK(v:ℝ)(B:Side):ℝ:=v/2/ feeG (8*B.val)
def rateH(v w:ℝ)(B:Side):= feeG (8*B.val)*quartzK v w
omit H G he
lemma ratePos (v:ℝ)(p:0<v)(B:Side):0<rateK v B:=by unfold rateK feeG; positivity
lemma rate_nonneg (a w:ℝ)(B:Side)(h:0≤ w):0≤ rateH a w B:=mul_nonneg (by unfold feeG; positivity) (qp a w h)
include H G he ha hw
lemma packB(u:Bool){i:ℕ}(p':i<n): Seat (forestB m B e p|>.botL) (fun x=>facePay j l n M m B (stampA x) (solesK u x) (tided u x) (stick 1) i) (rateK a B) (rateH a w B):=by
 let K:=earnings (repeated j) (repeated j) l M (idrat (CSide m B)); -- m variable l correct
 let R:=idrat (CSide m B); let F:= vertexP R (A:=K) (H.stock M R rfl he) ha H.posT
 let X :ℕ:=8*B.val; have hx:0<X:= mul_pos (by decide) B.property; let Z:=foam (Domain m B) X; have hX:0<feeG X:=by unfold feeG; positivity
 apply Seat.shop (b:=weave R d) (c:=(forestB m B e p).botL) (Φ:=Z) (X:=fun x:Loom R d=> Matrix.trace (K (post x.val))) (v:=feeG X) (w:=feeG X) (foams X hx _) F (beckL u i p' H G) (beck_c H G u p') (qp a w hw.le) (ratePos _ ha B).le ?_ ?_ ?_
 · exact le_of_eq (div_mul_cancel₀ (a/2) hX.ne')
 · intro S x y q; let f:=foam_in (Domain m B) X S; let g:Agrees S (stampA x) (stampA y):=fun i l H=> q.1.1 i (f l) (f H); have he: cloudG R S=S:=by ext; simp [R,cloudG,filed]
   change Agrees S (stampA x) (stampA y)∧Agrees (cloudG R S) (stampA x) (stampA y)∧AgreeF S (ticketX u (i+1) n x) (ticketX u (i+1) n y)∧AgreeF (cloudG R S) (ticketX u i n x) (ticketX u i n y); rw [he]; exact ⟨g,g,local_arc u (i+1) n S x y q,local_arc u i n S x y q⟩
 intro x y; refine ⟨y,Subtype.ext ?_⟩
 let Z:=(forestB m B e p).pool y x; change couple (stampA Z) (ticketX u i n Z) (ticketX u (i+1) n Z)=frost _ y (rollP u i n x);
 rw [fare_c H G he _ x y i p'.le, fare_c H G he _ x y (i+1) p']; exact gazeG H.stock H.posT he ..
section generic
omit H G he ha hw
variable {β χ I D: Type*}[DecidableEq I][Fintype I][TopologicalSpace D]{S:Light I D β}
lemma flattenS (v: Finset χ)(A:χ→ D→ℂ)(h:∀ i∈v,Seat S (A i) a d):Seat S (fun x=> ∑ i∈v,A i x) a (v.card*d):=by
 classical
 induction v using Finset.induction_on with
 | empty=> exact ⟨fun _ _=>0,fun _=>0,⟨fun S=> Peak.emptyB,fun i=>by simp [hitE]⟩,by simp⟩
 | @insert i t e ih=>
   have he:=ih (fun i p=>h _ (by simp [p])); simp only [sum_insert e,card_insert_of_notMem e,Nat.cast_add_one, add_mul,one_mul]; rw [add_comm (_*d)]; exact (h i (by simp)).adds he
-- monomials scalar contractions. cost sign
lemma Seat.minus {f:D→ℂ}(h:Seat S f a d): Seat S (fun i=> -f i) a d:=by
 let L := -(ContinuousLinearMap.id ℝ ℂ); have ht:= h.frameH L 1 (by simp [L]); rw [one_mul] at ht; exact ht
end generic
lemma tariffs(u:Bool):Seat ((forestB m B e p).botL) (fun i=>antler j l n M m B (stampA i) (tided u i) (brim i)) (rateK a B) ((n:ℝ)*rateH a w B):=by
  have he:= flattenS (Finset.range n) (fun i (x:backS m B e p)=>facePay j l n M m B (stampA x) (solesK u x) (tided u x) (stick 1) i) (fun i hi=>packB H ha hw G he M u (mem_range.mp hi)); rw [Finset.card_range] at he; exact he
lemma balanceJ : Seat (foamK (CSide m B) e p) (fun x=> lick j l n M m B x.val.1 x.val.2.1 x.val.2.2) (rateK a B) ((n:ℝ)*rateH a w B + (n:ℝ)*rateH a w B):= by
 letI : LocallyCompactSpace ↑(BinK (CSide m B) e p):=local_cpn ..
 let H':=forestB m B e p; let A:=ranK m B e p; let F:=fun x:backS m B e p=> hero j l n M m B (stampA x) (tided false x) (tided true x) (brim x)
 have hv: Seat H'.botL F (rateK a B) ((n:ℝ)*rateH a w B+(n:ℝ)*rateH a w B):=by
   unfold F hero; simp_rw [sub_eq_add_neg]; exact (tariffs H ha hw G he M false).adds ((tariffs H ha hw G he M true).minus)
 have hx:=H'.loot hv (complexA m B) (fun x T=>cover_s m B T x) (fun _=>subset_refl _) (fun T x y h=> overB m B x y h)
 convert hx using 1; funext x
 let K:= lick j l n M m B x.val.1 x.val.2.1 x.val.2.2
 have hy(y):cream A F (x,y)=fall (A x) y • K:=by
   by_cases p:fall (A x) y≠0; swap; rw [not_not] at p; unfold cream; change fall (A x) y • _=fall (A x) y • _; rw [p,zero_smul,zero_smul]
   let f: Sam A:= ⟨(x,y),p⟩
   have he' : F f= K :=(priceHero H G he x.property.1 x.property.2.1 x.property.2.2 (sealS m B (f:backS m B _ _)) M).symm
   exact congrArg (fun v:ℂ=>fall (A x) y • v) ((sampler_p (A:=A) F (x,y) p).trans he')
 change K=means A F x; unfold means; simp_rw [hy]; rw [integral_smul_const,sails_all,one_smul]
end YM.CF.Broc
