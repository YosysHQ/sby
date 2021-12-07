from xmlschema import XMLSchema, XMLSchemaValidationError
import argparse

def main():
    parser = argparse.ArgumentParser(description="Validate JUnit output")
    parser.add_argument('xml')
    parser.add_argument('--xsd', default="JUnit.xsd")

    args = parser.parse_args()

    schema = XMLSchema(args.xsd)
    try:
        schema.validate(args.xml)
    except XMLSchemaValidationError as e:
        print(e)
        exit(1)

if __name__ == '__main__':
    main()
