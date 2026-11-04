// Native intrinsic observations, separate from kernel-checked model refinements.
if (Bun.version !== '1.4.0') throw new Error('Use pinned Bun 1.4.0')
const document = JSON.parse(await Bun.stdin.text())
const fromUnits = (units: number[]): string => {
  let text = ''
  for (const unit of units) text += String.fromCharCode(unit)
  return text
}
const toUnits = (text: string): number[] => {
  const units = []
  for (let index = 0; index < text.length; index++) units.push(text.charCodeAt(index))
  return units
}
const tagged = (value: string | undefined) => value === undefined
  ? { undefined: true } : { string: toUnits(value) }
const arrays = document.arrays.map((input: number[][]) => {
  const array = input.map(fromUnits)
  const indices = [0, 1, array.length, array.length + 1]
  const get = indices.map(index => tagged(array[index]))
  const equalsEmpty = indices.map(index => array[index] === '')
  const oldLength = array.length
  const alias = array
  const first = alias.shift()
  if (alias !== array) throw new Error('Lost native alias')
  return { first: tagged(first), after: array.map(toUnits), indices, get, equalsEmpty,
    length: array.length, oldLastIsOwn: Object.hasOwn(array, Math.max(0, oldLength - 1)) }
})
const split = document.inputs.map((input: number[]) =>
  fromUnits(input).split(fromUnits([document.separator]), document.limit).map(toUnits))
const paths = document.inputs.map((input: number[]) => {
  const fields = fromUnits(input).split('/', document.limit)
  if (fields[0] === '') fields.shift()
  return fields.map(toUnits)
})
console.log(JSON.stringify({ split, paths, arrays }))
