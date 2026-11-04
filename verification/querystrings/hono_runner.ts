// Finite native source evidence. Source identity is checked before import by tests.py.
if (Bun.version !== '1.4.0') throw new Error('Use pinned Bun 1.4.0')
const { getQueryStrings } = await import(Bun.argv[2])
const document = JSON.parse(await Bun.stdin.text())
const fromUnits = (units: number[]): string => {
  let value = ''
  for (const unit of units) value += String.fromCharCode(unit)
  return value
}
const toUnits = (value: string): number[] => {
  const result = []
  for (let index = 0; index < value.length; index++) result.push(value.charCodeAt(index))
  return result
}
const primitives = (document.primitives ?? []).map((input: any) => {
  const value = fromUnits(input.units)
  return { index: value.indexOf(fromUnits([input.separator]), input.position),
    slice: toUnits(input.stop === null ? value.slice(input.start) : value.slice(input.start, input.stop)) }
})
console.log(JSON.stringify({ runtime: Bun.version, primitives,
  results: (document.inputs ?? []).map((input: number[]) => toUnits(getQueryStrings(fromUnits(input)))) }))
